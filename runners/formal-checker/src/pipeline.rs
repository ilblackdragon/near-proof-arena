//! The formal-check pipeline:
//!
//! * Reference build (judge-only content): trusted packages + generated
//!   `Expected` module → reference `.olean`s + reference NDJSON export.
//! * Stage A (untrusted): candidate `.lean` sources elaborated offline in the
//!   sandbox against the read-only reference `.olean`s. The candidate's
//!   lakefile is never used; the judge computes the build plan.
//! * Stage B (clean recheck): fresh sandboxes that never load candidate
//!   plugins: `leanchecker` replays candidate modules through the Lean kernel;
//!   `lean4export` exports the certificate's closure; `nanoda` (independent
//!   Rust kernel) checks that export.
//! * Stage C (judge checks): `arena-audit` (Environment API) and the Rust
//!   NDJSON audit against the reference export; they must agree.

use crate::audit::{self, LeanAudit};
use crate::digest::{json_digest, sha256_file, tree_digest};
use crate::expected::ExpectedTypeBuilder;
use crate::findings::{lossy_tail, Finding, Scope};
use crate::ndjson::Export;
use crate::report::{self, FormalCheckReport, GateSpec, RecheckerRun, Timing};
use crate::sandbox::{RunExit, RunOutcome, RunSpec, UntrustedRunner, CAPTURE_LIMIT, REPORT_CAPTURE_LIMIT};
use crate::staging::{self, CandidateModule, StagingPolicy};
use crate::toolchain::{lean_toolchain, ToolPaths};
use arena_types::{Digest, EvidenceRef, ObligationId, ReasonCode};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

pub const REPORT_SCHEMA: &str = "arena-formal-check-v1";

/// A judge-pinned Lean source package (formal-core, spec, stand-ins in tests).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TrustedPackage {
    pub name: String,
    /// Directory whose `.lean` files (module = relative path) form the package.
    pub src_root: PathBuf,
    /// Module-name prefixes to take from `src_root` (`None` = every module).
    #[serde(default)]
    pub include: Option<Vec<String>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Policy {
    /// Exact axioms permitted (challenge `toolchain_policy.axiom_allowlist`).
    pub axiom_allowlist: Vec<String>,
    /// Rechecker ids that must run and accept (`leanchecker`, `nanoda`).
    pub required_recheckers: Vec<String>,
    pub gates: Vec<GateSpec>,
    /// If the statement is a conjunction `C0 ∧ (C1 ∧ …)`, the gate each
    /// conjunct discharges (enables per-conjunct axiom attribution).
    pub conjunct_gates: Option<Vec<ObligationId>>,
    /// Extra module prefixes reserved for the judge (trusted package module
    /// prefixes, the Expected module and `ArenaAudit` are always reserved).
    pub reserved_prefixes: Vec<String>,
    /// Toolchain module prefixes candidates may import.
    pub toolchain_prefixes: Vec<String>,
    /// Lake package names candidate lakefiles may `require`.
    pub allowed_requires: Vec<String>,
}

impl Default for Policy {
    fn default() -> Self {
        Policy {
            axiom_allowlist: vec!["propext".into(), "Quot.sound".into(), "Classical.choice".into()],
            required_recheckers: vec!["leanchecker".into(), "nanoda".into()],
            gates: report::default_gates(),
            conjunct_gates: None,
            reserved_prefixes: vec![],
            toolchain_prefixes: vec!["Init".into(), "Std".into(), "Lean".into()],
            allowed_requires: vec![],
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Limits {
    pub module_timeout: Duration,
    pub elaboration_budget: Duration,
    pub recheck_timeout: Duration,
    pub audit_timeout: Duration,
    pub export_max_bytes: u64,
    pub mem_bytes: Option<u64>,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            module_timeout: Duration::from_secs(600),
            elaboration_budget: Duration::from_secs(1800),
            recheck_timeout: Duration::from_secs(1200),
            audit_timeout: Duration::from_secs(600),
            export_max_bytes: 4 << 30,
            mem_bytes: None,
        }
    }
}

pub struct CheckRequest<'a> {
    /// Candidate `formal/` directory (already extracted by the archive layer).
    pub formal_dir: PathBuf,
    /// Lean constant name from `candidate.toml` `[formal].certificate`.
    pub certificate: String,
    pub trusted: Vec<TrustedPackage>,
    pub expected: &'a dyn ExpectedTypeBuilder,
    /// Challenge definition digest (bound into the cache key).
    pub challenge_digest: Option<Digest>,
    pub policy: Policy,
    pub limits: Limits,
    /// Scratch directory for this check (created; must be empty or absent).
    pub work_dir: PathBuf,
    /// Judge-owned cache for reference builds (keyed by content digests).
    pub cache_dir: PathBuf,
}

pub struct FormalChecker {
    pub tools: ToolPaths,
    pub runner: Box<dyn UntrustedRunner>,
}

// Guest paths inside the sandbox.
const G_TC: &str = "/arena/tc";
const G_SRC: &str = "/arena/src";
const G_OUT: &str = "/arena/out";
const G_TRUSTED: &str = "/arena/trusted";
const G_CAND: &str = "/arena/cand";
const G_X: &str = "/arena/x";
const G_EXPORT: &str = "/arena/tools/lean4export";
const G_AUDIT: &str = "/arena/tools/arena-audit";
const G_NANODA: &str = "/arena/tools/nanoda_bin";
const G_L4L: &str = "/arena/tools/lean4lean";

struct Ctx<'a> {
    fc: &'a FormalChecker,
    timings: Vec<Timing>,
}

impl<'a> Ctx<'a> {
    fn base_spec(&self, argv: Vec<String>, lean_path: &str, timeout: Duration, mem: Option<u64>) -> RunSpec {
        let t = &self.fc.tools;
        let mut ro = vec![
            (t.lean_sysroot.clone(), PathBuf::from(G_TC)),
            (t.lean4export.clone(), PathBuf::from(G_EXPORT)),
            (t.arena_audit.clone(), PathBuf::from(G_AUDIT)),
        ];
        if let Some(n) = &t.nanoda {
            ro.push((n.clone(), PathBuf::from(G_NANODA)));
        }
        if let Some(n) = &t.lean4lean {
            ro.push((n.clone(), PathBuf::from(G_L4L)));
        }
        RunSpec {
            argv,
            env: vec![
                ("PATH".into(), format!("{G_TC}/bin:/usr/bin:/bin")),
                ("HOME".into(), "/tmp".into()),
                ("LEAN_PATH".into(), lean_path.into()),
                ("ARENA_LEAN_SYSROOT".into(), G_TC.into()),
                ("LEAN_ABORT_ON_PANIC".into(), "1".into()),
            ],
            ro,
            rw: vec![],
            cwd: PathBuf::from("/tmp"),
            wall_timeout: timeout,
            mem_bytes: mem,
            max_file_bytes: 8 << 30,
            stdout_file: None,
        }
    }

    fn run(&mut self, step: &str, spec: &RunSpec, cap: usize) -> Result<RunOutcome, Finding> {
        let r = self.fc.runner.run(spec, cap);
        match r {
            Ok(o) => {
                self.timings.push(Timing { step: step.into(), wall_ms: o.wall.as_millis() as u64 });
                Ok(o)
            }
            Err(e) => Err(Finding::unknown(ReasonCode::InfraError, format!("{step}: {e}"))),
        }
    }
}

fn now_rfc3339() -> String {
    time::OffsetDateTime::now_utc()
        .format(&time::format_description::well_known::Rfc3339)
        .unwrap_or_default()
}

/// Copy every `.lean` file under `root` into `dest`; returns module graph.
fn collect_trusted(pkg: &TrustedPackage, dest: &Path) -> Result<Vec<CandidateModule>, String> {
    let entries = crate::digest::list_tree(&pkg.src_root).map_err(|e| format!("{}: {e}", pkg.name))?;
    let mut mods = Vec::new();
    for e in entries {
        let Some(stem) = e.path.strip_suffix(".lean") else { continue };
        if stem == "lakefile" || e.path.starts_with(".lake/") {
            continue;
        }
        let comps: Vec<&str> = stem.split('/').collect();
        let name = comps.join(".");
        if let Some(inc) = &pkg.include {
            if !inc.iter().any(|p| staging::has_prefix(&name, p)) {
                continue;
            }
        }
        if !comps.iter().all(|c| staging::is_ident(c)) {
            return Err(format!("trusted package {}: bad module path {}", pkg.name, e.path));
        }
        let src = std::fs::read_to_string(pkg.src_root.join(&e.path)).map_err(|e| e.to_string())?;
        let (imports, _) = staging::parse_header(&src)?;
        let t = dest.join(&e.path);
        std::fs::create_dir_all(t.parent().unwrap()).map_err(|e| e.to_string())?;
        std::fs::write(&t, src).map_err(|e| e.to_string())?;
        mods.push(CandidateModule { name: comps.join("."), rel_path: e.path.clone(), imports });
    }
    Ok(mods)
}

fn topo(mods: Vec<CandidateModule>) -> Result<Vec<CandidateModule>, String> {
    use std::collections::BTreeMap;
    let map: BTreeMap<String, CandidateModule> = mods.into_iter().map(|m| (m.name.clone(), m)).collect();
    let mut state: BTreeMap<String, u8> = BTreeMap::new();
    let mut order = Vec::new();
    fn go(n: &str, map: &BTreeMap<String, CandidateModule>, st: &mut BTreeMap<String, u8>, out: &mut Vec<String>) -> Result<(), String> {
        match st.get(n) {
            Some(2) => return Ok(()),
            Some(1) => return Err(format!("import cycle at {n}")),
            _ => {}
        }
        st.insert(n.into(), 1);
        for i in &map[n].imports {
            if map.contains_key(i) {
                go(i, map, st, out)?;
            }
        }
        st.insert(n.into(), 2);
        out.push(n.into());
        Ok(())
    }
    for n in map.keys() {
        go(n, &map, &mut state, &mut order)?;
    }
    Ok(order.into_iter().map(|n| map[&n].clone()).collect())
}

/// Populate `dest` with symlinks `dest/<p> -> /arena/trusted/<p>` for every
/// file of the judge's reference output. Lean resolves a module through the
/// *first* search-path root containing its top-level directory, so trusted
/// and candidate modules sharing a namespace root (e.g. `Toy.Spec` vs
/// `Toy.Programs`) must live under one root. Symlinks point at the read-only
/// mount, so a sandboxed process can at most replace its own link, never the
/// judge's bytes (no hardlinks: they would alias the pristine inode).
fn link_trusted(trusted_out: &Path, dest: &Path) -> std::io::Result<()> {
    for e in crate::digest::list_tree(trusted_out).map_err(std::io::Error::other)? {
        let to = dest.join(&e.path);
        std::fs::create_dir_all(to.parent().unwrap())?;
        let _ = std::fs::remove_file(&to);
        std::os::unix::fs::symlink(Path::new(G_TRUSTED).join(&e.path), &to)?;
    }
    Ok(())
}

/// Compile modules in order with `lean` inside the sandbox.
fn compile(
    ctx: &mut Ctx,
    label: &str,
    mods: &[CandidateModule],
    src: &Path,
    out: &Path,
    trusted_ro: Option<&Path>,
    limits: &Limits,
) -> Result<(), Finding> {
    let start = Instant::now();
    if let Some(t) = trusted_ro {
        link_trusted(t, out).map_err(|e| Finding::unknown(ReasonCode::InfraError, format!("link trusted: {e}")))?;
    }
    let lean_path = G_OUT.to_string();
    for m in mods {
        let stem = m.rel_path.trim_end_matches(".lean");
        if let Some(parent) = out.join(stem).parent() {
            std::fs::create_dir_all(parent).map_err(|e| Finding::unknown(ReasonCode::InfraError, e.to_string()))?;
        }
        let remaining = limits.elaboration_budget.saturating_sub(start.elapsed());
        let timeout = remaining.min(limits.module_timeout);
        let argv = vec![
            format!("{G_TC}/bin/lean"),
            "-R".into(),
            G_SRC.into(),
            "-o".into(),
            format!("{G_OUT}/{stem}.olean"),
            "-i".into(),
            format!("{G_OUT}/{stem}.ilean"),
            format!("{G_SRC}/{}", m.rel_path),
        ];
        let mut spec = ctx.base_spec(argv, &lean_path, timeout, limits.mem_bytes);
        spec.ro.push((src.to_path_buf(), G_SRC.into()));
        if let Some(t) = trusted_ro {
            spec.ro.push((t.to_path_buf(), G_TRUSTED.into()));
        }
        spec.rw.push((out.to_path_buf(), G_OUT.into()));
        let o = ctx.run(&format!("{label}:elaborate:{}", m.name), &spec, CAPTURE_LIMIT)?;
        match o.exit {
            RunExit::Exited(0) => {}
            RunExit::TimedOut => {
                return Err(Finding::unknown(ReasonCode::Timeout, format!("{label}: elaboration of {} timed out", m.name)))
            }
            _ => {
                let mut msg = lossy_tail(&o.stdout, 1500);
                msg.push_str(&lossy_tail(&o.stderr, 500));
                return Err(Finding::new(
                    ReasonCode::BuildFailed,
                    Scope::All,
                    format!("{label}: module {} failed to elaborate ({:?}):\n{msg}", m.name, o.exit),
                ));
            }
        }
    }
    Ok(())
}

struct Reference {
    dir: PathBuf,
    out: PathBuf,
    modules: Vec<String>,
    export: Export,
    export_digest: Digest,
    trusted_digests: Vec<(String, Digest)>,
    expected_source_digest: Digest,
}

impl FormalChecker {
    pub fn new(tools: ToolPaths, runner: Box<dyn UntrustedRunner>) -> Self {
        FormalChecker { tools, runner }
    }

    fn reference(&self, ctx: &mut Ctx, req: &CheckRequest, image: &Digest) -> Result<Reference, Finding> {
        let infra = |e: String| Finding::unknown(ReasonCode::InfraError, format!("reference build: {e}"));
        let expected_src = req.expected.render().map_err(|e| infra(e.to_string()))?;
        let expected_source_digest = Digest::of_bytes(expected_src.as_bytes());
        let mut trusted_digests = Vec::new();
        for p in &req.trusted {
            trusted_digests.push((p.name.clone(), tree_digest(&p.src_root).map_err(|e| infra(e.to_string()))?));
        }
        let key = json_digest(&(
            "ref-v1",
            &trusted_digests,
            &expected_source_digest,
            image,
            &req.policy.axiom_allowlist,
            req.expected.decl_name(),
        ));
        let dir = req.cache_dir.join(format!("ref-{}", &key.hex()[..24]));
        let out = dir.join("out");
        let export_path = dir.join("reference.ndjson");
        let modules_path = dir.join("modules.json");
        if !dir.join("done").is_file() {
            // Build in a private temp dir, then publish atomically by rename
            // (concurrent checks may race to build the same reference).
            let final_dir = dir.clone();
            let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
            let dir = req.cache_dir.join(format!(".tmp-ref-{}-{}-{nanos}", &key.hex()[..24], std::process::id()));
            let out = dir.join("out");
            let export_path = dir.join("reference.ndjson");
            let modules_path = dir.join("modules.json");
            let src = dir.join("src");
            std::fs::create_dir_all(&src).map_err(|e| infra(e.to_string()))?;
            std::fs::create_dir_all(&out).map_err(|e| infra(e.to_string()))?;
            let mut mods = Vec::new();
            for p in &req.trusted {
                mods.extend(collect_trusted(p, &src).map_err(infra)?);
            }
            let exp_rel = format!("{}.lean", req.expected.module_name().replace('.', "/"));
            let exp_path = src.join(&exp_rel);
            std::fs::create_dir_all(exp_path.parent().unwrap()).map_err(|e| infra(e.to_string()))?;
            std::fs::write(&exp_path, &expected_src).map_err(|e| infra(e.to_string()))?;
            let (imports, _) = staging::parse_header(&expected_src).map_err(infra)?;
            mods.push(CandidateModule { name: req.expected.module_name().into(), rel_path: exp_rel, imports });
            let mods = topo(mods).map_err(infra)?;
            compile(ctx, "reference", &mods, &src, &out, None, &req.limits).map_err(|f| infra(f.detail))?;
            let modules: Vec<String> = mods.iter().map(|m| m.name.clone()).collect();
            // Names of every constant in trusted modules.
            let cfg = serde_json::json!({
                "imports": modules, "expectedDecl": req.expected.decl_name(), "certificate": "",
                "candidateModules": [], "trustedModules": modules,
                "toolchainPrefixes": req.policy.toolchain_prefixes,
            });
            let cfg_dir = dir.join("cfg");
            std::fs::create_dir_all(&cfg_dir).map_err(|e| infra(e.to_string()))?;
            std::fs::write(cfg_dir.join("list.json"), cfg.to_string()).map_err(|e| infra(e.to_string()))?;
            let mut spec = ctx.base_spec(
                vec![G_AUDIT.into(), "list-trusted".into(), format!("{G_X}/list.json")],
                G_TRUSTED,
                req.limits.audit_timeout,
                None,
            );
            spec.ro.push((out.clone(), G_TRUSTED.into()));
            spec.ro.push((cfg_dir.clone(), G_X.into()));
            let o = ctx.run("reference:list-trusted", &spec, REPORT_CAPTURE_LIMIT).map_err(|f| infra(f.detail))?;
            if !o.success() {
                return Err(infra(format!("list-trusted failed: {}", lossy_tail(&o.stderr, 800))));
            }
            let v: serde_json::Value = serde_json::from_slice(&o.stdout).map_err(|e| infra(e.to_string()))?;
            let mut names: Vec<String> = v["constants"]
                .as_array()
                .map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect())
                .unwrap_or_default();
            names.retain(|n| !n.starts_with('_') && !n.contains("._") && !n.contains('«'));
            names.extend(req.policy.axiom_allowlist.iter().cloned());
            names.push(req.expected.decl_name().into());
            let mut argv = vec![G_EXPORT.to_string()];
            argv.extend(modules.iter().cloned());
            argv.push("--".into());
            argv.extend(names);
            let mut spec = ctx.base_spec(argv, G_TRUSTED, req.limits.recheck_timeout, None);
            spec.ro.push((out.clone(), G_TRUSTED.into()));
            spec.stdout_file = Some(export_path.clone());
            let o = ctx.run("reference:export", &spec, CAPTURE_LIMIT).map_err(|f| infra(f.detail))?;
            if !o.success() {
                return Err(infra(format!("reference export failed: {}", lossy_tail(&o.stderr, 800))));
            }
            std::fs::write(&modules_path, serde_json::to_string(&modules).unwrap()).map_err(|e| infra(e.to_string()))?;
            std::fs::write(dir.join("done"), b"ok").map_err(|e| infra(e.to_string()))?;
            if !final_dir.join("done").is_file() {
                let _ = std::fs::remove_dir_all(&final_dir);
            }
            if std::fs::rename(&dir, &final_dir).is_err() {
                let _ = std::fs::remove_dir_all(&dir);
                if !final_dir.join("done").is_file() {
                    return Err(infra("could not publish reference build".into()));
                }
            }
        }
        let modules: Vec<String> = serde_json::from_slice(&std::fs::read(&modules_path).map_err(|e| infra(e.to_string()))?)
            .map_err(|e| infra(e.to_string()))?;
        let t = Instant::now();
        let export = Export::read(&export_path, req.limits.export_max_bytes).map_err(|e| infra(e.to_string()))?;
        ctx.timings.push(Timing { step: "reference:parse".into(), wall_ms: t.elapsed().as_millis() as u64 });
        let export_digest = sha256_file(&export_path).map_err(|e| infra(e.to_string()))?;
        Ok(Reference { dir, out, modules, export, export_digest, trusted_digests, expected_source_digest })
    }

    /// Run the full pipeline. Never panics on candidate input; every failure
    /// mode maps to FAIL (definite) or UNKNOWN (undecided), never PASS.
    pub fn check(&self, req: &CheckRequest) -> FormalCheckReport {
        let started = now_rfc3339();
        let mut ctx = Ctx { fc: self, timings: vec![] };
        let mut findings: Vec<Finding> = Vec::new();
        let mut warnings: Vec<String> = Vec::new();
        let mut rechecks: Vec<RecheckerRun> = Vec::new();
        let mut evidence: Vec<EvidenceRef> = Vec::new();
        let mut closure_report = None;
        let mut graph_type_ok = false;
        let mut cert_digest = None;
        let mut graph_axioms: Vec<String> = vec![];

        let image = self.tools.image_digest().unwrap_or_else(|_| Digest::of_bytes(b"unknown-image"));
        let formal_tree = tree_digest(&req.formal_dir).ok();
        let _ = std::fs::remove_dir_all(&req.work_dir);
        let _ = std::fs::create_dir_all(&req.work_dir);

        let reference = self.reference(&mut ctx, req, &image);
        let cache_key = json_digest(&serde_json::json!({
            "schema": REPORT_SCHEMA,
            "checker_version": env!("CARGO_PKG_VERSION"),
            "toolchain": lean_toolchain(),
            "checker_image": image,
            "formal_tree": formal_tree,
            "trusted": reference.as_ref().ok().map(|r| r.trusted_digests.clone()),
            "expected_source": reference.as_ref().ok().map(|r| r.expected_source_digest.clone()),
            "certificate": req.certificate,
            "challenge": req.challenge_digest,
            "policy": req.policy,
        }));

        'pipeline: {
            let reference = match reference {
                Ok(r) => r,
                Err(f) => {
                    findings.push(f);
                    break 'pipeline;
                }
            };
            evidence.push(EvidenceRef { label: "reference export (ndjson)".into(), digest: reference.export_digest.clone(), public: true });
            if formal_tree.is_none() {
                findings.push(Finding::new(ReasonCode::ArchiveUnsafe, Scope::All, "formal tree unreadable or contains unsupported entries".into()));
            }

            // ---------------- Stage A: static staging + sandboxed elaboration
            let mut reserved: Vec<String> = req.policy.reserved_prefixes.clone();
            // Exact trusted module names (and their sub-modules) are reserved;
            // whole namespaces only via `policy.reserved_prefixes` (e.g. `ArenaCore`),
            // so a challenge spec module `Toy.Spec` does not reserve `Toy.*`.
            reserved.extend(reference.modules.iter().cloned());
            reserved.push(req.expected.module_name().into());
            reserved.push("ArenaAudit".into());
            reserved.sort();
            reserved.dedup();
            let pol = StagingPolicy {
                reserved_prefixes: reserved,
                toolchain_prefixes: req.policy.toolchain_prefixes.clone(),
                allowed_requires: req.policy.allowed_requires.clone(),
                trusted_modules: reference.modules.clone(),
            };
            let cand_src = req.work_dir.join("cand-src");
            let cand_out = req.work_dir.join("cand-out");
            let _ = std::fs::create_dir_all(&cand_src);
            let _ = std::fs::create_dir_all(&cand_out);
            let staged = match staging::stage_candidate(&req.formal_dir, &cand_src, &pol) {
                Ok(s) => s,
                Err(e) => {
                    findings.push(Finding::unknown(ReasonCode::InfraError, format!("staging: {e}")));
                    break 'pipeline;
                }
            };
            warnings.extend(staged.warnings.iter().cloned());
            warnings.extend(crate::grep::scan(&cand_src, &staged.modules.iter().map(|m| m.rel_path.clone()).collect::<Vec<_>>()));
            if report::has_fail(&staged.findings) {
                findings.extend(staged.findings);
                break 'pipeline;
            }
            if let Err(f) = compile(&mut ctx, "candidate", &staged.modules, &cand_src, &cand_out, Some(&reference.out), &req.limits) {
                findings.push(f);
                if findings.iter().any(|f| f.code == ReasonCode::BuildFailed) {
                    findings.push(Finding::new(ReasonCode::CertificateMissing, Scope::All, "candidate project does not build; certificate unavailable".into()));
                }
                break 'pipeline;
            }
            let cand_mods: Vec<String> = staged.modules.iter().map(|m| m.name.clone()).collect();

            // ---------------- Stage B: clean recheck on a fresh copy of the
            // candidate's .olean files only (nothing else the elaboration wrote).
            let replay = req.work_dir.join("replay");
            let replay_oleans = replay.join("oleans");
            let x = replay.join("x");
            let _ = std::fs::create_dir_all(&replay_oleans);
            let _ = std::fs::create_dir_all(&x);
            for m in &staged.modules {
                let stem = m.rel_path.trim_end_matches(".lean");
                for suffix in [".olean", ".olean.server", ".olean.private"] {
                    let from = cand_out.join(format!("{stem}{suffix}"));
                    // Never follow links planted by the sandboxed build (they
                    // could point at host files): regular files only.
                    let regular = std::fs::symlink_metadata(&from).map(|m| m.file_type().is_file()).unwrap_or(false);
                    if from.exists() && !regular {
                        findings.push(Finding::new(ReasonCode::SandboxViolation, Scope::All, format!("build output {stem}{suffix} is not a regular file")));
                        break 'pipeline;
                    }
                    if regular {
                        let to = replay_oleans.join(format!("{stem}{suffix}"));
                        let _ = std::fs::create_dir_all(to.parent().unwrap());
                        if let Err(e) = std::fs::copy(&from, &to) {
                            findings.push(Finding::unknown(ReasonCode::InfraError, format!("copy olean: {e}")));
                            break 'pipeline;
                        }
                    }
                }
                if let Ok(d) = sha256_file(&replay_oleans.join(format!("{stem}.olean"))) {
                    evidence.push(EvidenceRef { label: format!("candidate olean {}", m.name), digest: d, public: true });
                }
            }
            if let Err(e) = link_trusted(&reference.out, &replay_oleans) {
                findings.push(Finding::unknown(ReasonCode::InfraError, format!("link trusted: {e}")));
                break 'pipeline;
            }
            let lean_path = G_CAND.to_string();
            let mount_replay = |spec: &mut RunSpec| {
                spec.ro.push((reference.out.clone(), G_TRUSTED.into()));
                spec.ro.push((replay_oleans.clone(), G_CAND.into()));
            };

            // B1: leanchecker (Lean kernel replay of every candidate module).
            {
                let mut argv = vec![format!("{G_TC}/bin/leanchecker")];
                argv.extend(cand_mods.iter().cloned());
                let mut spec = ctx.base_spec(argv, &lean_path, req.limits.recheck_timeout, req.limits.mem_bytes);
                mount_replay(&mut spec);
                rechecks.push(match ctx.run("recheck:leanchecker", &spec, CAPTURE_LIMIT) {
                    Err(f) => {
                        findings.push(f);
                        RecheckerRun { id: "leanchecker".into(), ran: false, verdict: "error".into(), wall_ms: 0, detail: "infra".into() }
                    }
                    Ok(o) => verdict("leanchecker", &o, &mut findings),
                });
            }

            // B2: export the certificate's closure (sandboxed: loads candidate oleans).
            let cand_export = x.join("candidate.ndjson");
            let export_ok = {
                let mut argv = vec![G_EXPORT.to_string()];
                argv.extend(cand_mods.iter().cloned());
                argv.push("--".into());
                argv.push(req.certificate.clone());
                let mut spec = ctx.base_spec(argv, &lean_path, req.limits.recheck_timeout, req.limits.mem_bytes);
                mount_replay(&mut spec);
                spec.stdout_file = Some(cand_export.clone());
                spec.max_file_bytes = req.limits.export_max_bytes;
                match ctx.run("recheck:lean4export", &spec, CAPTURE_LIMIT) {
                    Err(f) => {
                        findings.push(f);
                        false
                    }
                    Ok(o) if o.exit == RunExit::TimedOut => {
                        findings.push(Finding::unknown(ReasonCode::Timeout, "lean4export timed out".into()));
                        false
                    }
                    Ok(o) if !o.success() => {
                        warnings.push(format!("lean4export failed: {}", lossy_tail(&o.stderr, 600)));
                        false
                    }
                    Ok(_) => true,
                }
            };
            if export_ok {
                if let Ok(d) = sha256_file(&cand_export) {
                    evidence.push(EvidenceRef { label: "candidate certificate export (ndjson)".into(), digest: d, public: true });
                }
            }

            // B3: nanoda (independent kernel) on that export.
            let mut nanoda_count: Option<u64> = None;
            match (&self.tools.nanoda, export_ok) {
                (None, _) => rechecks.push(RecheckerRun {
                    id: "nanoda".into(),
                    ran: false,
                    verdict: "not_run".into(),
                    wall_ms: 0,
                    detail: "nanoda_bin not installed".into(),
                }),
                (Some(_), false) => rechecks.push(RecheckerRun {
                    id: "nanoda".into(),
                    ran: false,
                    verdict: "not_run".into(),
                    wall_ms: 0,
                    detail: "no export to check".into(),
                }),
                (Some(_), true) => {
                    let cfg = serde_json::json!({
                        "export_file_path": format!("{G_X}/candidate.ndjson"),
                        "use_stdin": false,
                        "unpermitted_axiom_hard_error": false,
                        "unsafe_permit_all_axioms": true,
                        "nat_extension": true,
                        "string_extension": true,
                        "print_success_message": true
                    });
                    let _ = std::fs::write(x.join("nanoda.json"), cfg.to_string());
                    let mut spec = ctx.base_spec(
                        vec![G_NANODA.into(), format!("{G_X}/nanoda.json")],
                        &lean_path,
                        req.limits.recheck_timeout,
                        req.limits.mem_bytes,
                    );
                    spec.ro.push((x.clone(), G_X.into()));
                    rechecks.push(match ctx.run("recheck:nanoda", &spec, CAPTURE_LIMIT) {
                        Err(f) => {
                            findings.push(f);
                            RecheckerRun { id: "nanoda".into(), ran: false, verdict: "error".into(), wall_ms: 0, detail: "infra".into() }
                        }
                        Ok(o) => {
                            let s = String::from_utf8_lossy(&o.stdout);
                            nanoda_count = s
                                .split("Checked ")
                                .nth(1)
                                .and_then(|r| r.split_whitespace().next())
                                .and_then(|n| n.parse().ok());
                            verdict("nanoda", &o, &mut findings)
                        }
                    });
                }
            }
            // B4: lean4lean (independent kernel implementation, .olean replay).
            if self.tools.lean4lean.is_some() {
                let mut argv = vec![G_L4L.to_string()];
                argv.extend(cand_mods.iter().cloned());
                let mut spec = ctx.base_spec(argv, &lean_path, req.limits.recheck_timeout, req.limits.mem_bytes);
                mount_replay(&mut spec);
                rechecks.push(match ctx.run("recheck:lean4lean", &spec, CAPTURE_LIMIT) {
                    Err(f) => {
                        findings.push(f);
                        RecheckerRun { id: "lean4lean".into(), ran: false, verdict: "error".into(), wall_ms: 0, detail: "infra".into() }
                    }
                    Ok(o) => verdict("lean4lean", &o, &mut findings),
                });
            } else {
                rechecks.push(RecheckerRun {
                    id: "lean4lean".into(),
                    ran: false,
                    verdict: "not_run".into(),
                    wall_ms: 0,
                    detail: format!("lean4lean not installed for {}", lean_toolchain()),
                });
            }
            for req_id in &req.policy.required_recheckers {
                let ok = rechecks.iter().any(|r| &r.id == req_id && r.ran);
                if !ok {
                    findings.push(Finding::unknown(ReasonCode::InfraError, format!("required rechecker {req_id} did not run")));
                }
            }

            // ---------------- Stage C: judge checks.
            let audit_cfg = serde_json::json!({
                "imports": std::iter::once(req.expected.module_name().to_string()).chain(cand_mods.iter().cloned()).collect::<Vec<_>>(),
                "expectedDecl": req.expected.decl_name(),
                "certificate": req.certificate,
                "candidateModules": cand_mods,
                "trustedModules": reference.modules,
                "toolchainPrefixes": req.policy.toolchain_prefixes,
            });
            let _ = std::fs::write(x.join("audit.json"), audit_cfg.to_string());
            let lean_audit: Option<LeanAudit> = {
                let mut spec = ctx.base_spec(
                    vec![G_AUDIT.into(), "check".into(), format!("{G_X}/audit.json")],
                    &lean_path,
                    req.limits.audit_timeout,
                    req.limits.mem_bytes,
                );
                mount_replay(&mut spec);
                spec.ro.push((x.clone(), G_X.into()));
                match ctx.run("audit:arena-audit", &spec, REPORT_CAPTURE_LIMIT) {
                    Err(f) => {
                        findings.push(f);
                        None
                    }
                    Ok(o) if o.exit == RunExit::TimedOut => {
                        findings.push(Finding::unknown(ReasonCode::Timeout, "arena-audit timed out".into()));
                        None
                    }
                    Ok(o) => match serde_json::from_slice::<LeanAudit>(&o.stdout) {
                        Ok(a) if o.success() => {
                            let _ = std::fs::write(req.work_dir.join("lean-audit.json"), &o.stdout);
                            evidence.push(EvidenceRef { label: "arena-audit report".into(), digest: Digest::of_bytes(&o.stdout), public: true });
                            rechecks.push(RecheckerRun { id: "arena-audit".into(), ran: true, verdict: "completed".into(), wall_ms: o.wall.as_millis() as u64, detail: String::new() });
                            Some(a)
                        }
                        _ => {
                            findings.push(Finding::new(
                                ReasonCode::RecheckFailed,
                                Scope::All,
                                format!("arena-audit failed on the candidate environment ({:?}): {}", o.exit, lossy_tail(&o.stderr, 600)),
                            ));
                            None
                        }
                    },
                }
            };
            let nd: Option<audit::NdAudit> = if export_ok {
                let t = Instant::now();
                match Export::read(&cand_export, req.limits.export_max_bytes) {
                    Ok(ex) => {
                        let n_conj = req.policy.conjunct_gates.as_ref().map_or(1, |c| c.len());
                        let a = audit::nd_audit(&ex, &reference.export, &req.certificate, req.expected.decl_name(), n_conj);
                        if let Some(n) = nanoda_count {
                            if n == 0 || (ex.decls.len() as u64) < n / 2 {
                                findings.push(Finding::new(
                                    ReasonCode::RecheckFailed,
                                    Scope::All,
                                    format!("nanoda checked {n} declarations but export has {}", ex.decls.len()),
                                ));
                            }
                        }
                        ctx.timings.push(Timing { step: "audit:ndjson".into(), wall_ms: t.elapsed().as_millis() as u64 });
                        rechecks.push(RecheckerRun { id: "ndjson-audit".into(), ran: true, verdict: "completed".into(), wall_ms: t.elapsed().as_millis() as u64, detail: format!("{} decls", ex.decls.len()) });
                        Some(a)
                    }
                    Err(e) => {
                        findings.push(Finding::new(ReasonCode::RecheckFailed, Scope::All, format!("candidate export unreadable: {e}")));
                        None
                    }
                }
            } else {
                None
            };
            let trusted_axioms = nd.as_ref().map(|a| a.trusted_axioms.clone()).unwrap_or_else(|| {
                reference
                    .export
                    .decls
                    .values()
                    .filter(|d| d.kind == crate::ndjson::DeclKind::Axiom)
                    .map(|d| d.name.clone())
                    .collect::<BTreeSet<_>>()
            });
            if let Some(la) = &lean_audit {
                let per_conjunct = nd.as_ref().is_some_and(|a| a.conjunct_axioms.is_some());
                findings.extend(audit::lean_findings(la, &req.policy.axiom_allowlist, &trusted_axioms, per_conjunct));
            }
            if let Some(a) = &nd {
                findings.extend(audit::nd_findings(a, &req.policy.axiom_allowlist));
                graph_type_ok = a.type_equal;
                graph_axioms = a.axioms.iter().cloned().collect();
                if let Some(c) = a.closure_digest.clone() {
                    cert_digest = Some(c.clone());
                    let listing = serde_json::to_vec(&a.closure).unwrap_or_default();
                    let _ = std::fs::write(req.work_dir.join("closure.json"), &listing);
                    let lref = EvidenceRef { label: "certificate dependency closure".into(), digest: Digest::of_bytes(&listing), public: true };
                    evidence.push(lref.clone());
                    closure_report = Some(report::ClosureReport {
                        certificate: req.certificate.clone(),
                        count: a.closure_count,
                        digest: Some(c),
                        axioms: graph_axioms.clone(),
                        listing: Some(lref),
                    });
                }
            } else if !export_ok {
                // No independent view of the environment: never PASS.
                let missing = lean_audit.as_ref().is_some_and(|l| l.certificate_found != Some(true));
                if !missing {
                    findings.push(Finding::new(ReasonCode::RecheckFailed, Scope::All, "certificate closure could not be exported for independent checking".into()));
                }
            }
            if let (Some(la), Some(a)) = (&lean_audit, &nd) {
                if let Some(f) = audit::cross_check(la, a) {
                    findings.push(f);
                }
            }
            if lean_audit.is_none() && !report::has_fail(&findings) {
                findings.push(Finding::unknown(ReasonCode::InfraError, "Lean-side audit unavailable".into()));
            }
            let _ = &reference.dir;
        }

        let findings = report::dedupe(findings);
        let finished = now_rfc3339();
        let gates = report::assemble_gates(
            &req.policy.gates,
            &findings,
            req.policy.conjunct_gates.as_deref(),
            &evidence,
            &started,
            &finished,
        );
        let trusted_list: Vec<(String, Digest)> = req
            .trusted
            .iter()
            .filter_map(|p| tree_digest(&p.src_root).ok().map(|d| (p.name.clone(), d)))
            .collect();
        let graph = report::evidence_graph(&report::GraphInput {
            certificate: &req.certificate,
            certificate_digest: cert_digest,
            statement_digest: req.expected.render().ok().map(|s| Digest::of_bytes(s.as_bytes())),
            trusted: &trusted_list,
            axioms: &graph_axioms,
            allowlist: &req.policy.axiom_allowlist,
            rechecks: &rechecks,
            type_ok: graph_type_ok && !report::has_fail(&findings),
            evidence: evidence.iter().map(|e| e.digest.clone()).collect(),
            toolchain_digest: image.clone(),
        });
        FormalCheckReport {
            schema: REPORT_SCHEMA,
            cache_key,
            lean_toolchain: lean_toolchain().into(),
            runner: self.runner.id().into(),
            tier_cap: self.runner.demo_only().then_some(arena_types::challenge::Tier::Demo),
            gates,
            findings,
            rechecks,
            closure: closure_report,
            evidence,
            evidence_graph: graph,
            warnings,
            timings: ctx.timings,
        }
    }
}

fn verdict(id: &str, o: &RunOutcome, findings: &mut Vec<Finding>) -> RecheckerRun {
    let wall_ms = o.wall.as_millis() as u64;
    let (v, detail) = match &o.exit {
        RunExit::Exited(0) => ("accepted", String::new()),
        RunExit::TimedOut => {
            findings.push(Finding::unknown(ReasonCode::Timeout, format!("{id} timed out")));
            ("timeout", String::new())
        }
        other => {
            let d = format!("{other:?}: {}{}", lossy_tail(&o.stdout, 400), lossy_tail(&o.stderr, 800));
            findings.push(Finding::new(ReasonCode::RecheckFailed, Scope::All, format!("{id} rejected the candidate environment: {d}")));
            ("rejected", d)
        }
    };
    RecheckerRun { id: id.into(), ran: true, verdict: v.into(), wall_ms, detail: crate::findings::bound(detail) }
}
