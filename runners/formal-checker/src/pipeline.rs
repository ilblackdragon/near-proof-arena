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
use crate::native::{self, NativeLeanRoute, NativeVerifierBuild, VerifierRoute};
use crate::ndjson::Export;
use crate::report::{self, FormalCheckReport, GateSpec, RecheckerRun, Timing};
use crate::sandbox::{
    RunExit, RunOutcome, RunSpec, UntrustedRunner, CAPTURE_LIMIT, REPORT_CAPTURE_LIMIT,
};
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
            axiom_allowlist: vec![
                "propext".into(),
                "Quot.sound".into(),
                "Classical.choice".into(),
            ],
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
    /// Wall timeout of one rechecker sandbox run.
    pub recheck_timeout: Duration,
    /// Candidate modules per `leanchecker` / `lean4lean` sandbox run. Both
    /// tools replay every module they are given as a parallel task, each
    /// importing its own environment, so memory grows with the number of
    /// modules per run (≈60 GB for a 100-module candidate in one run); runs
    /// are sequential and the verdict is the conjunction.
    pub recheck_batch_modules: usize,
    /// Total wall budget of all batches of one module rechecker.
    pub recheck_total: Duration,
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
            recheck_batch_modules: 1,
            recheck_total: Duration::from_secs(3600),
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
    /// How the verifier executable is bound to the statement.
    pub route: VerifierRoute,
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
    fn base_spec(
        &self,
        argv: Vec<String>,
        lean_path: &str,
        timeout: Duration,
        mem: Option<u64>,
    ) -> RunSpec {
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
                self.timings.push(Timing {
                    step: step.into(),
                    wall_ms: o.wall.as_millis() as u64,
                });
                Ok(o)
            }
            Err(e) => Err(Finding::unknown(
                ReasonCode::InfraError,
                format!("{step}: {e}"),
            )),
        }
    }
}

/// Lean reports a candidate redefinition of a trusted name as an import
/// collision; classify that as shadowing rather than a generic failure.
fn shadow_or(output: &str, otherwise: ReasonCode) -> ReasonCode {
    if output.contains("already contains")
        || output.contains("already declared")
        || output.contains("has already been declared")
    {
        ReasonCode::ShadowedDefinition
    } else {
        otherwise
    }
}

fn now_rfc3339() -> String {
    time::OffsetDateTime::now_utc()
        .format(&time::format_description::well_known::Rfc3339)
        .unwrap_or_default()
}

/// Copy every `.lean` file under `root` into `dest`; returns module graph.
fn collect_trusted(pkg: &TrustedPackage, dest: &Path) -> Result<Vec<CandidateModule>, String> {
    let entries =
        crate::digest::list_tree(&pkg.src_root).map_err(|e| format!("{}: {e}", pkg.name))?;
    let mut mods = Vec::new();
    for e in entries {
        let Some(stem) = e.path.strip_suffix(".lean") else {
            continue;
        };
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
            return Err(format!(
                "trusted package {}: bad module path {}",
                pkg.name, e.path
            ));
        }
        let src = std::fs::read_to_string(pkg.src_root.join(&e.path)).map_err(|e| e.to_string())?;
        let (imports, _) = staging::parse_header(&src)?;
        let t = dest.join(&e.path);
        std::fs::create_dir_all(t.parent().unwrap()).map_err(|e| e.to_string())?;
        std::fs::write(&t, src).map_err(|e| e.to_string())?;
        mods.push(CandidateModule {
            name: comps.join("."),
            rel_path: e.path.clone(),
            imports,
        });
    }
    Ok(mods)
}

fn topo(mods: Vec<CandidateModule>) -> Result<Vec<CandidateModule>, String> {
    use std::collections::BTreeMap;
    let map: BTreeMap<String, CandidateModule> =
        mods.into_iter().map(|m| (m.name.clone(), m)).collect();
    let mut state: BTreeMap<String, u8> = BTreeMap::new();
    let mut order = Vec::new();
    fn go(
        n: &str,
        map: &BTreeMap<String, CandidateModule>,
        st: &mut BTreeMap<String, u8>,
        out: &mut Vec<String>,
    ) -> Result<(), String> {
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
#[allow(clippy::too_many_arguments)]
fn compile(
    ctx: &mut Ctx,
    label: &str,
    mods: &[CandidateModule],
    src: &Path,
    out: &Path,
    trusted_ro: Option<&Path>,
    limits: &Limits,
    emit_c: bool,
) -> Result<(), Finding> {
    let start = Instant::now();
    if let Some(t) = trusted_ro {
        link_trusted(t, out)
            .map_err(|e| Finding::unknown(ReasonCode::InfraError, format!("link trusted: {e}")))?;
    }
    let lean_path = G_OUT.to_string();
    for m in mods {
        let stem = m.rel_path.trim_end_matches(".lean");
        if let Some(parent) = out.join(stem).parent() {
            std::fs::create_dir_all(parent)
                .map_err(|e| Finding::unknown(ReasonCode::InfraError, e.to_string()))?;
        }
        let remaining = limits.elaboration_budget.saturating_sub(start.elapsed());
        let timeout = remaining.min(limits.module_timeout);
        let mut argv = vec![
            format!("{G_TC}/bin/lean"),
            "-R".into(),
            G_SRC.into(),
            "-o".into(),
            format!("{G_OUT}/{stem}.olean"),
            "-i".into(),
            format!("{G_OUT}/{stem}.ilean"),
        ];
        if emit_c {
            argv.push("-c".into());
            argv.push(format!("{G_OUT}/{stem}.c"));
        }
        argv.push(format!("{G_SRC}/{}", m.rel_path));
        let mut spec = ctx.base_spec(argv, &lean_path, timeout, limits.mem_bytes);
        spec.ro.push((src.to_path_buf(), G_SRC.into()));
        if let Some(t) = trusted_ro {
            spec.ro.push((t.to_path_buf(), G_TRUSTED.into()));
        }
        spec.rw.push((out.to_path_buf(), G_OUT.into()));
        let o = ctx.run(
            &format!("{label}:elaborate:{}", m.name),
            &spec,
            CAPTURE_LIMIT,
        )?;
        match o.exit {
            RunExit::Exited(0) => {}
            RunExit::TimedOut => {
                return Err(Finding::unknown(
                    ReasonCode::Timeout,
                    format!("{label}: elaboration of {} timed out", m.name),
                ))
            }
            _ => {
                let mut msg = lossy_tail(&o.stdout, 1500);
                msg.push_str(&lossy_tail(&o.stderr, 500));
                return Err(Finding::new(
                    ReasonCode::BuildFailed,
                    Scope::All,
                    format!(
                        "{label}: module {} failed to elaborate ({:?}):\n{msg}",
                        m.name, o.exit
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// Elaborate one module (emitting C) in a sandbox run whose only writable
/// directory is a fresh `iso` dir; imports resolve through the read-only
/// `lib` root. Output files are checked to be regular files.
#[allow(clippy::too_many_arguments)]
fn compile_isolated(
    ctx: &mut Ctx,
    label: &str,
    m: &CandidateModule,
    src: &Path,
    lib: &Path,
    trusted_out: &Path,
    iso: &Path,
    limits: &Limits,
) -> Result<PathBuf, Finding> {
    let _ = std::fs::remove_dir_all(iso);
    let stem = m.rel_path.trim_end_matches(".lean");
    std::fs::create_dir_all(iso.join(stem).parent().unwrap())
        .map_err(|e| Finding::unknown(ReasonCode::InfraError, e.to_string()))?;
    let argv = vec![
        format!("{G_TC}/bin/lean"),
        "-R".into(),
        G_SRC.into(),
        "-o".into(),
        format!("{G_OUT}/{stem}.olean"),
        "-c".into(),
        format!("{G_OUT}/{stem}.c"),
        format!("{G_SRC}/{}", m.rel_path),
    ];
    let mut spec = ctx.base_spec(argv, "/arena/lib", limits.module_timeout, limits.mem_bytes);
    spec.ro.push((src.to_path_buf(), G_SRC.into()));
    spec.ro.push((trusted_out.to_path_buf(), G_TRUSTED.into()));
    spec.ro.push((lib.to_path_buf(), "/arena/lib".into()));
    spec.rw.push((iso.to_path_buf(), G_OUT.into()));
    let o = ctx.run(
        &format!("{label}:elaborate:{}", m.name),
        &spec,
        CAPTURE_LIMIT,
    )?;
    match o.exit {
        RunExit::Exited(0) => {}
        RunExit::TimedOut => {
            return Err(Finding::unknown(
                ReasonCode::Timeout,
                format!("{label}: elaboration of {} timed out", m.name),
            ))
        }
        _ => {
            let mut msg = lossy_tail(&o.stdout, 1500);
            msg.push_str(&lossy_tail(&o.stderr, 500));
            return Err(Finding::new(
                shadow_or(&msg, ReasonCode::BuildFailed),
                Scope::All,
                format!(
                    "{label}: module {} failed to elaborate ({:?}):\n{msg}",
                    m.name, o.exit
                ),
            ));
        }
    }
    for suffix in [".olean", ".c"] {
        let p = iso.join(format!("{stem}{suffix}"));
        let regular = std::fs::symlink_metadata(&p)
            .map(|x| x.file_type().is_file())
            .unwrap_or(false);
        if !regular {
            return Err(Finding::new(
                ReasonCode::SandboxViolation,
                Scope::All,
                format!("{label}: output {stem}{suffix} missing or not a regular file"),
            ));
        }
    }
    Ok(iso.to_path_buf())
}

struct TrustedBuild {
    /// Judge-built trusted `.olean`s and C files.
    out: PathBuf,
    modules: Vec<String>,
    digests: Vec<(String, Digest)>,
}

struct Reference {
    out: PathBuf,
    /// Trusted modules + the Expected module.
    modules: Vec<String>,
    export: Export,
    export_digest: Digest,
    expected_source_digest: Digest,
}

/// Build into a private temp dir, then publish atomically by rename
/// (concurrent checks may race to build the same cache entry).
fn cached_build(
    cache_dir: &Path,
    name: &str,
    build: impl FnOnce(&Path) -> Result<(), String>,
) -> Result<PathBuf, String> {
    let dir = cache_dir.join(name);
    if dir.join("done").is_file() {
        return Ok(dir);
    }
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let tmp = cache_dir.join(format!(".tmp-{name}-{}-{nanos}", std::process::id()));
    std::fs::create_dir_all(&tmp).map_err(|e| e.to_string())?;
    if let Err(e) = build(&tmp) {
        let _ = std::fs::remove_dir_all(&tmp);
        return Err(e);
    }
    std::fs::write(tmp.join("done"), b"ok").map_err(|e| e.to_string())?;
    if !dir.join("done").is_file() {
        let _ = std::fs::remove_dir_all(&dir);
    }
    if std::fs::rename(&tmp, &dir).is_err() {
        let _ = std::fs::remove_dir_all(&tmp);
        if !dir.join("done").is_file() {
            return Err("could not publish cache entry".into());
        }
    }
    Ok(dir)
}

fn copy_tree(from: &Path, to: &Path) -> std::io::Result<()> {
    for e in crate::digest::list_tree(from).map_err(std::io::Error::other)? {
        let t = to.join(&e.path);
        std::fs::create_dir_all(t.parent().unwrap())?;
        std::fs::copy(from.join(&e.path), &t)?;
    }
    Ok(())
}

impl FormalChecker {
    pub fn new(tools: ToolPaths, runner: Box<dyn UntrustedRunner>) -> Self {
        FormalChecker { tools, runner }
    }

    /// Phase 1 (judge-only content): compile the pinned trusted packages.
    fn trusted_build(
        &self,
        ctx: &mut Ctx,
        req: &CheckRequest,
        image: &Digest,
    ) -> Result<TrustedBuild, Finding> {
        let infra =
            |e: String| Finding::unknown(ReasonCode::InfraError, format!("trusted build: {e}"));
        let mut digests = Vec::new();
        for p in &req.trusted {
            digests.push((
                p.name.clone(),
                tree_digest(&p.src_root).map_err(|e| infra(e.to_string()))?,
            ));
        }
        let includes: Vec<_> = req.trusted.iter().map(|p| (&p.name, &p.include)).collect();
        let key = json_digest(&("trusted-v2", &digests, &includes, image));
        let dir = cached_build(&req.cache_dir, &format!("tr-{}", &key.hex()[..24]), |dir| {
            let src = dir.join("src");
            let out = dir.join("out");
            std::fs::create_dir_all(&src).map_err(|e| e.to_string())?;
            std::fs::create_dir_all(&out).map_err(|e| e.to_string())?;
            let mut mods = Vec::new();
            for p in &req.trusted {
                mods.extend(collect_trusted(p, &src)?);
            }
            let mods = topo(mods)?;
            compile(ctx, "trusted", &mods, &src, &out, None, &req.limits, true)
                .map_err(|f| f.detail)?;
            let names: Vec<String> = mods.iter().map(|m| m.name.clone()).collect();
            std::fs::write(
                dir.join("modules.json"),
                serde_json::to_string(&names).unwrap(),
            )
            .map_err(|e| e.to_string())
        })
        .map_err(infra)?;
        let modules: Vec<String> = serde_json::from_slice(
            &std::fs::read(dir.join("modules.json")).map_err(|e| infra(e.to_string()))?,
        )
        .map_err(|e| infra(e.to_string()))?;
        Ok(TrustedBuild {
            out: dir.join("out"),
            modules,
            digests,
        })
    }

    /// Phase 2 (judge-only content): the generated Expected module on top of
    /// the trusted build, plus the reference export.
    fn reference(
        &self,
        ctx: &mut Ctx,
        req: &CheckRequest,
        image: &Digest,
        tb: &TrustedBuild,
        expected_src: &str,
    ) -> Result<Reference, Finding> {
        let infra =
            |e: String| Finding::unknown(ReasonCode::InfraError, format!("reference build: {e}"));
        let expected_source_digest = Digest::of_bytes(expected_src.as_bytes());
        let key = json_digest(&(
            "ref-v2",
            &tb.digests,
            &expected_source_digest,
            image,
            &req.policy.axiom_allowlist,
            req.expected.decl_name(),
            req.expected.module_name(),
        ));
        let mut all_modules = tb.modules.clone();
        all_modules.push(req.expected.module_name().into());
        let dir = cached_build(&req.cache_dir, &format!("ref-{}", &key.hex()[..24]), |dir| {
            let src = dir.join("src");
            let out = dir.join("out");
            std::fs::create_dir_all(&src).map_err(|e| e.to_string())?;
            copy_tree(&tb.out, &out).map_err(|e| e.to_string())?;
            let exp_rel = format!("{}.lean", req.expected.module_name().replace('.', "/"));
            let exp_path = src.join(&exp_rel);
            std::fs::create_dir_all(exp_path.parent().unwrap()).map_err(|e| e.to_string())?;
            std::fs::write(&exp_path, expected_src).map_err(|e| e.to_string())?;
            let (imports, _) = staging::parse_header(expected_src)?;
            let m = CandidateModule { name: req.expected.module_name().into(), rel_path: exp_rel, imports };
            compile(ctx, "reference", &[m], &src, &out, None, &req.limits, false).map_err(|f| f.detail)?;
            // Names of every constant in trusted modules (incl. Expected).
            let cfg = serde_json::json!({
                "imports": all_modules, "expectedDecl": req.expected.decl_name(), "certificate": "",
                "candidateModules": [], "trustedModules": all_modules,
                "toolchainPrefixes": req.policy.toolchain_prefixes, "modelDecl": "", "instDecl": "",
            });
            let cfg_dir = dir.join("cfg");
            std::fs::create_dir_all(&cfg_dir).map_err(|e| e.to_string())?;
            std::fs::write(cfg_dir.join("list.json"), cfg.to_string()).map_err(|e| e.to_string())?;
            let mut spec = ctx.base_spec(
                vec![G_AUDIT.into(), "list-trusted".into(), format!("{G_X}/list.json")],
                G_TRUSTED,
                req.limits.audit_timeout,
                None,
            );
            spec.ro.push((out.clone(), G_TRUSTED.into()));
            spec.ro.push((cfg_dir.clone(), G_X.into()));
            let o = ctx.run("reference:list-trusted", &spec, REPORT_CAPTURE_LIMIT).map_err(|f| f.detail)?;
            if !o.success() {
                return Err(format!("list-trusted failed: {}", lossy_tail(&o.stderr, 800)));
            }
            let v: serde_json::Value = serde_json::from_slice(&o.stdout).map_err(|e| e.to_string())?;
            let mut names: Vec<String> = v["constants"]
                .as_array()
                .map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect())
                .unwrap_or_default();
            names.retain(|n| !n.starts_with('_') && !n.contains("._") && !n.contains('«'));
            names.extend(req.policy.axiom_allowlist.iter().cloned());
            names.push(req.expected.decl_name().into());
            let mut argv = vec![G_EXPORT.to_string()];
            argv.extend(all_modules.iter().cloned());
            argv.push("--".into());
            argv.extend(names);
            let mut spec = ctx.base_spec(argv, G_TRUSTED, req.limits.recheck_timeout, None);
            spec.ro.push((out.clone(), G_TRUSTED.into()));
            spec.stdout_file = Some(dir.join("reference.ndjson"));
            let o = ctx.run("reference:export", &spec, CAPTURE_LIMIT).map_err(|f| f.detail)?;
            if !o.success() {
                return Err(format!("reference export failed: {}", lossy_tail(&o.stderr, 800)));
            }
            Ok(())
        })
        .map_err(infra)?;
        let export_path = dir.join("reference.ndjson");
        let t = Instant::now();
        let export = Export::read(&export_path, req.limits.export_max_bytes)
            .map_err(|e| infra(e.to_string()))?;
        ctx.timings.push(Timing {
            step: "reference:parse".into(),
            wall_ms: t.elapsed().as_millis() as u64,
        });
        let export_digest = sha256_file(&export_path).map_err(|e| infra(e.to_string()))?;
        Ok(Reference {
            out: dir.join("out"),
            modules: all_modules,
            export,
            export_digest,
            expected_source_digest,
        })
    }

    /// Judge build of the native verifier from the candidate model.
    ///
    /// Hardened against compile-time tampering by candidate code:
    /// * every module is elaborated in its own sandbox run whose only writable
    ///   directory is that module's fresh output dir (a candidate `#eval` can
    ///   at most corrupt its own module's outputs, never trusted C/objects);
    /// * trusted modules' C comes from the judge-only trusted build;
    /// * model-closure modules may import only trusted modules, other model
    ///   modules and `Init` (no `Lean`/`Std`/`Lake` metaprogramming: nothing can
    ///   rewrite the compiler's IR behind the kernel definition);
    /// * the judge `main` wrapper is elaborated twice — with the candidate
    ///   model in scope and against a judge stub axiom of the same name and
    ///   type — and the two must be identical (candidate syntax/macros cannot
    ///   alter the wrapper);
    /// * C → objects → executable happen in judge-only sandbox runs.
    #[allow(clippy::too_many_arguments)]
    fn native_build(
        &self,
        ctx: &mut Ctx,
        req: &CheckRequest,
        route: &NativeLeanRoute,
        tb: &TrustedBuild,
        cand_src: &Path,
        cand_out: &Path,
        model_mods: &[CandidateModule],
    ) -> Result<NativeVerifierBuild, Finding> {
        let infra =
            |e: String| Finding::unknown(ReasonCode::InfraError, format!("native build: {e}"));
        let bind = |msg: String| Finding::new(ReasonCode::ArtifactBindingFailed, Scope::All, msg);
        for m in model_mods {
            for i in &m.imports {
                let ok = tb.modules.contains(i)
                    || model_mods.iter().any(|x| &x.name == i)
                    || staging::has_prefix(i, "Init");
                if !ok {
                    return Err(bind(format!(
                        "verifier model module {} imports {i}: model modules may import only trusted modules, other model modules and Init (no metaprogramming in code the judge compiles)",
                        m.name
                    )));
                }
            }
        }
        let nb = req.work_dir.join("native");
        let _ = std::fs::remove_dir_all(&nb);
        let lib = nb.join("lib");
        let cdir = nb.join("c");
        for d in [&lib, &cdir] {
            std::fs::create_dir_all(d).map_err(|e| infra(e.to_string()))?;
        }
        link_trusted(&tb.out, &lib).map_err(|e| infra(e.to_string()))?;
        let mut c_files: Vec<String> = Vec::new();
        for m in &tb.modules {
            let stem = m.replace('.', "/");
            std::fs::copy(
                tb.out.join(format!("{stem}.c")),
                cdir.join(format!("{m}.c")),
            )
            .map_err(|e| infra(format!("trusted C for {m}: {e}")))?;
            c_files.push(m.clone());
        }
        // Model closure, isolated per module.
        for m in model_mods {
            let iso = compile_isolated(
                ctx,
                "model",
                m,
                cand_src,
                &lib,
                &tb.out,
                &nb.join("iso").join(&m.name),
                &req.limits,
            )?;
            let stem = m.rel_path.trim_end_matches(".lean");
            for suffix in [".olean", ".olean.server", ".olean.private"] {
                let from = iso.join(format!("{stem}{suffix}"));
                if from.exists() {
                    for dest in [&lib, &cand_out.to_path_buf()] {
                        let to = dest.join(format!("{stem}{suffix}"));
                        std::fs::create_dir_all(to.parent().unwrap())
                            .map_err(|e| infra(e.to_string()))?;
                        let _ = std::fs::remove_file(&to);
                        std::fs::copy(&from, &to).map_err(|e| infra(e.to_string()))?;
                    }
                }
            }
            std::fs::copy(
                iso.join(format!("{stem}.c")),
                cdir.join(format!("{}.c", m.name)),
            )
            .map_err(|e| infra(e.to_string()))?;
            c_files.push(m.name.clone());
        }
        // Judge wrapper, with the candidate model in scope.
        let main_mod = "ArenaVerifyMain";
        let main_src_dir = nb.join("main-src");
        std::fs::create_dir_all(&main_src_dir).map_err(|e| infra(e.to_string()))?;
        let main_src =
            native::render_main(&route.main_template, &route.model_module, &route.model_decl);
        std::fs::write(main_src_dir.join(format!("{main_mod}.lean")), &main_src)
            .map_err(|e| infra(e.to_string()))?;
        let (main_imports, _) = staging::parse_header(&main_src).map_err(infra)?;
        let main_m = CandidateModule {
            name: main_mod.into(),
            rel_path: format!("{main_mod}.lean"),
            imports: main_imports.clone(),
        };
        let iso = compile_isolated(
            ctx,
            "wrapper",
            &main_m,
            &main_src_dir,
            &lib,
            &tb.out,
            &nb.join("iso").join(main_mod),
            &req.limits,
        )
        .map_err(|f| {
            if f.severity == crate::findings::Severity::Fail
                && f.code != ReasonCode::ShadowedDefinition
            {
                bind(format!(
                    "judge verify wrapper does not elaborate against the model: {}",
                    f.detail
                ))
            } else {
                f
            }
        })?;
        std::fs::copy(
            iso.join(format!("{main_mod}.olean")),
            lib.join(format!("{main_mod}.olean")),
        )
        .map_err(|e| infra(e.to_string()))?;
        std::fs::copy(
            iso.join(format!("{main_mod}.c")),
            cdir.join(format!("{main_mod}.c")),
        )
        .map_err(|e| infra(e.to_string()))?;
        c_files.push(main_mod.into());
        // Same wrapper against a judge stub (judge-only content).
        let stub = nb.join("stub");
        let stub_src = stub.join("src");
        let stub_lib = stub.join("lib");
        std::fs::create_dir_all(&stub_src).map_err(|e| infra(e.to_string()))?;
        std::fs::create_dir_all(&stub_lib).map_err(|e| infra(e.to_string()))?;
        let stub_rel = format!("{}.lean", route.model_module.replace('.', "/"));
        let stub_text = format!(
            "import {}\n\n/-! judge stub of the candidate model (same name and type) -/\naxiom {} : {}\n",
            route.model_type_module, route.model_decl, route.model_type
        );
        std::fs::create_dir_all(stub_src.join(&stub_rel).parent().unwrap())
            .map_err(|e| infra(e.to_string()))?;
        std::fs::write(stub_src.join(&stub_rel), &stub_text).map_err(|e| infra(e.to_string()))?;
        // The stub model is an axiom (no code), so the stub wrapper is
        // elaborated as `noncomputable`: kernel declarations are unchanged.
        let header_end = main_src
            .lines()
            .take_while(|l| l.starts_with("import ") || l.trim().is_empty())
            .map(|l| l.len() + 1)
            .sum::<usize>();
        let stub_main = format!(
            "{}noncomputable section\n{}",
            &main_src[..header_end],
            &main_src[header_end..]
        );
        std::fs::write(stub_src.join(format!("{main_mod}.lean")), &stub_main)
            .map_err(|e| infra(e.to_string()))?;
        let stub_mods = vec![
            CandidateModule {
                name: route.model_module.clone(),
                rel_path: stub_rel,
                imports: vec![route.model_type_module.clone()],
            },
            main_m.clone(),
        ];
        compile(
            ctx,
            "wrapper-stub",
            &stub_mods,
            &stub_src,
            &stub_lib,
            Some(&tb.out),
            &req.limits,
            false,
        )
        .map_err(|f| infra(format!("stub wrapper: {}", f.detail)))?;
        let dump = |ctx: &mut Ctx, lib_dir: &Path, tag: &str| -> Result<Vec<u8>, Finding> {
            let cfg = serde_json::json!({
                "imports": [main_mod], "expectedDecl": "", "certificate": "", "candidateModules": [],
                "trustedModules": [main_mod], "toolchainPrefixes": [], "modelDecl": "", "instDecl": "",
            });
            let cfg_dir = nb.join(format!("dump-{tag}"));
            std::fs::create_dir_all(&cfg_dir).map_err(|e| infra(e.to_string()))?;
            std::fs::write(cfg_dir.join("cfg.json"), cfg.to_string())
                .map_err(|e| infra(e.to_string()))?;
            let mut spec = ctx.base_spec(
                vec![G_AUDIT.into(), "dump".into(), format!("{G_X}/cfg.json")],
                "/arena/lib",
                req.limits.audit_timeout,
                req.limits.mem_bytes,
            );
            spec.ro.push((tb.out.clone(), G_TRUSTED.into()));
            spec.ro.push((lib_dir.to_path_buf(), "/arena/lib".into()));
            spec.ro.push((cfg_dir, G_X.into()));
            let o = ctx.run(&format!("native:dump-{tag}"), &spec, REPORT_CAPTURE_LIMIT)?;
            if !o.success() {
                return Err(bind(format!(
                    "wrapper dump ({tag}) failed: {}",
                    lossy_tail(&o.stderr, 600)
                )));
            }
            Ok(o.stdout)
        };
        let real = dump(ctx, &lib, "real")?;
        let stubbed = dump(ctx, &stub_lib, "stub")?;
        if real != stubbed || real.len() < 10 {
            return Err(bind(
                "the judge verify wrapper elaborates differently with the candidate model in scope than against the judge stub (candidate syntax/macros/instances altered it)".into(),
            ));
        }
        // C -> objects -> executable (judge-only runs).
        let odir = nb.join("o");
        std::fs::create_dir_all(&odir).map_err(|e| infra(e.to_string()))?;
        for m in &c_files {
            let mut spec = ctx.base_spec(
                vec![
                    format!("{G_TC}/bin/leanc"),
                    "-c".into(),
                    "-O3".into(),
                    "-DNDEBUG".into(),
                    format!("/arena/c/{m}.c"),
                    "-o".into(),
                    format!("/arena/o/{m}.o"),
                ],
                "",
                req.limits.module_timeout,
                req.limits.mem_bytes,
            );
            spec.ro.push((cdir.clone(), "/arena/c".into()));
            spec.rw.push((odir.clone(), "/arena/o".into()));
            let o = ctx.run(&format!("native:cc:{m}"), &spec, CAPTURE_LIMIT)?;
            if !o.success() {
                return Err(bind(format!(
                    "C compilation of {m} failed: {}",
                    lossy_tail(&o.stderr, 800)
                )));
            }
        }
        let mut argv = vec![
            format!("{G_TC}/bin/leanc"),
            "-o".into(),
            "/arena/o/verify".into(),
        ];
        argv.extend(c_files.iter().map(|m| format!("/arena/o/{m}.o")));
        let mut spec = ctx.base_spec(argv, "", req.limits.module_timeout, req.limits.mem_bytes);
        spec.rw.push((odir.clone(), "/arena/o".into()));
        let o = ctx.run("native:link", &spec, CAPTURE_LIMIT)?;
        if !o.success() {
            return Err(bind(format!(
                "linking the native verifier failed: {}",
                lossy_tail(&o.stderr, 800)
            )));
        }
        let built = odir.join("verify");
        let regular = std::fs::symlink_metadata(&built)
            .map(|m| m.file_type().is_file())
            .unwrap_or(false);
        if !regular {
            return Err(Finding::new(
                ReasonCode::SandboxViolation,
                Scope::All,
                "native build output is not a regular file".into(),
            ));
        }
        let path = req.work_dir.join("verify");
        std::fs::copy(&built, &path).map_err(|e| infra(e.to_string()))?;
        let digest = sha256_file(&path).map_err(|e| infra(e.to_string()))?;
        Ok(NativeVerifierBuild {
            path,
            digest,
            toolchain_id: route.toolchain_id.clone(),
            lean_toolchain: lean_toolchain().into(),
            model_decl: route.model_decl.clone(),
        })
    }

    /// Run the full pipeline. Never panics on candidate input; every failure
    /// mode maps to FAIL (definite) or UNKNOWN (undecided), never PASS.
    pub fn check(&self, req: &CheckRequest) -> FormalCheckReport {
        let started = now_rfc3339();
        let mut ctx = Ctx {
            fc: self,
            timings: vec![],
        };
        let mut findings: Vec<Finding> = Vec::new();
        let mut warnings: Vec<String> = Vec::new();
        let mut rechecks: Vec<RecheckerRun> = Vec::new();
        let mut evidence: Vec<EvidenceRef> = Vec::new();
        let mut closure_report = None;
        let mut graph_type_ok = false;
        let mut cert_digest = None;
        let mut graph_axioms: Vec<String> = vec![];

        let image = self
            .tools
            .image_digest()
            .unwrap_or_else(|_| Digest::of_bytes(b"unknown-image"));
        let formal_tree = tree_digest(&req.formal_dir).ok();
        let _ = std::fs::remove_dir_all(&req.work_dir);
        let _ = std::fs::create_dir_all(&req.work_dir);

        let trusted_build = self.trusted_build(&mut ctx, req, &image);
        let cache_key = json_digest(&serde_json::json!({
            "schema": REPORT_SCHEMA,
            "checker_version": env!("CARGO_PKG_VERSION"),
            "toolchain": lean_toolchain(),
            "checker_image": image,
            "formal_tree": formal_tree,
            "trusted": trusted_build.as_ref().ok().map(|t| t.digests.clone()),
            "expected": req.expected.identity(),
            "certificate": req.certificate,
            "challenge": req.challenge_digest,
            "policy": req.policy,
            "route": req.route,
        }));
        let model_route = match &req.route {
            VerifierRoute::NativeLean(r) => Some(r),
            _ => None,
        };
        let mut native_build: Option<NativeVerifierBuild> = None;
        let mut statement_digest: Option<Digest> = None;
        let mut model_report: Option<report::ModelReport> = None;

        'pipeline: {
            let tb = match trusted_build {
                Ok(t) => t,
                Err(f) => {
                    findings.push(f);
                    break 'pipeline;
                }
            };
            if matches!(req.route, VerifierRoute::CandidateNative) {
                findings.push(Finding::new(
                    ReasonCode::ArtifactBindingFailed,
                    Scope::All,
                    "candidate-built native verifier: no route binds a candidate binary to the statement (use verify_route = \"native-lean\" so the judge builds it from the model)".into(),
                ));
                break 'pipeline;
            }
            if req.certificate.is_empty() || !req.certificate.split('.').all(staging::is_ident) {
                findings.push(Finding::new(
                    ReasonCode::ManifestInvalid,
                    Scope::All,
                    format!(
                        "certificate name {:?} is not a plain dotted Lean identifier",
                        req.certificate
                    ),
                ));
                break 'pipeline;
            }
            if let Some(r) = model_route {
                let ok = |x: &str| !x.is_empty() && x.split('.').all(staging::is_ident);
                if !(ok(&r.model_decl)
                    && ok(&r.model_module)
                    && ok(&r.inst_module)
                    && ok(&r.inst_decl))
                {
                    findings.push(Finding::new(
                        ReasonCode::ManifestInvalid,
                        Scope::All,
                        "verifier model names must be dotted Lean identifiers".into(),
                    ));
                    break 'pipeline;
                }
                // `model_type_module` is spliced into a judge-compiled `import`
                // and `model_type` into a judge-compiled `axiom … : <type>`
                // stub (see `native_build`). They are judge/challenge-set
                // today, but validate their shape here so a future caller that
                // forwards candidate input cannot inject Lean syntax (extra
                // commands, newlines) into code the judge compiles and links.
                if !ok(&r.model_type_module) {
                    findings.push(Finding::new(
                        ReasonCode::ManifestInvalid,
                        Scope::All,
                        "verifier model_type_module must be a dotted Lean identifier".into(),
                    ));
                    break 'pipeline;
                }
                // A type expression is richer than an identifier, but it must
                // stay a single-line type: no newlines (would start a new Lean
                // command after the stub `axiom`), no comment or string
                // delimiters, printable ASCII only.
                let type_bad = r.model_type.is_empty()
                    || r.model_type.contains(['\n', '\r', '"'])
                    || r.model_type.contains("--")
                    || r.model_type.contains("/-")
                    || r.model_type.chars().any(|c| !(' '..='~').contains(&c));
                if type_bad {
                    findings.push(Finding::new(
                        ReasonCode::ManifestInvalid,
                        Scope::All,
                        "verifier model_type must be a single-line printable-ASCII Lean type"
                            .into(),
                    ));
                    break 'pipeline;
                }
            }
            if formal_tree.is_none() {
                findings.push(Finding::new(
                    ReasonCode::ArchiveUnsafe,
                    Scope::All,
                    "formal tree unreadable or contains unsupported entries".into(),
                ));
            }

            // ---------------- Stage A: static staging + sandboxed elaboration
            let mut judge_modules: Vec<String> = tb.modules.clone();
            judge_modules.push(req.expected.module_name().into());
            if let Some(r) = model_route {
                judge_modules.push(r.inst_module.clone());
            }
            let mut reserved: Vec<String> = req.policy.reserved_prefixes.clone();
            // Exact trusted module names (and their sub-modules) are reserved;
            // whole namespaces only via `policy.reserved_prefixes` (e.g. `ArenaCore`),
            // so a challenge spec module `Toy.Spec` does not reserve `Toy.*`.
            reserved.extend(judge_modules.iter().cloned());
            reserved.push("ArenaAudit".into());
            reserved.push("ArenaVerifyMain".into());
            reserved.sort();
            reserved.dedup();
            let pol = StagingPolicy {
                reserved_prefixes: reserved,
                toolchain_prefixes: req.policy.toolchain_prefixes.clone(),
                allowed_requires: req.policy.allowed_requires.clone(),
                trusted_modules: judge_modules.clone(),
            };
            let cand_src = req.work_dir.join("cand-src");
            let cand_out = req.work_dir.join("cand-out");
            let _ = std::fs::create_dir_all(&cand_src);
            let _ = std::fs::create_dir_all(&cand_out);
            let staged = match staging::stage_candidate(&req.formal_dir, &cand_src, &pol) {
                Ok(s) => s,
                Err(e) => {
                    findings.push(Finding::unknown(
                        ReasonCode::InfraError,
                        format!("staging: {e}"),
                    ));
                    break 'pipeline;
                }
            };
            warnings.extend(staged.warnings.iter().cloned());
            warnings.extend(crate::grep::scan(
                &cand_src,
                &staged
                    .modules
                    .iter()
                    .map(|m| m.rel_path.clone())
                    .collect::<Vec<_>>(),
            ));
            if report::has_fail(&staged.findings) {
                findings.extend(staged.findings);
                break 'pipeline;
            }
            let build_failed = |findings: &mut Vec<Finding>, f: Finding| {
                let is_build = f.code == ReasonCode::BuildFailed;
                findings.push(f);
                if is_build {
                    findings.push(Finding::new(
                        ReasonCode::CertificateMissing,
                        Scope::All,
                        "candidate project does not build; certificate unavailable".into(),
                    ));
                }
            };

            // A0 (native-lean): the model and its candidate dependencies are
            // compiled FIRST, against the trusted build only; the judge then
            // builds the native verifier from it and only then renders the
            // statement (which pins the judge build's digest).
            let mut compiled: BTreeSet<String> = BTreeSet::new();
            let mut extra = std::collections::BTreeMap::new();
            if let Some(r) = model_route {
                if !staged.modules.iter().any(|m| m.name == r.model_module) {
                    findings.push(Finding::new(
                        ReasonCode::ArtifactBindingFailed,
                        Scope::All,
                        format!(
                            "verifier model module {} is not part of the candidate formal tree",
                            r.model_module
                        ),
                    ));
                    break 'pipeline;
                }
                // Transitive candidate imports of the model module.
                let mut need: BTreeSet<String> = BTreeSet::new();
                let mut stack = vec![r.model_module.clone()];
                while let Some(n) = stack.pop() {
                    if !need.insert(n.clone()) {
                        continue;
                    }
                    if let Some(m) = staged.modules.iter().find(|m| m.name == n) {
                        for i in &m.imports {
                            if i == req.expected.module_name() || i == &r.inst_module {
                                findings.push(Finding::new(
                                    ReasonCode::ArtifactBindingFailed,
                                    Scope::All,
                                    format!("verifier model closure module {n} imports the judge statement {i} (the model must not depend on the statement)"),
                                ));
                                break 'pipeline;
                            }
                            if staged.modules.iter().any(|m| &m.name == i) {
                                stack.push(i.clone());
                            }
                        }
                    }
                }
                let model_mods: Vec<CandidateModule> = staged
                    .modules
                    .iter()
                    .filter(|m| need.contains(&m.name))
                    .cloned()
                    .collect();
                let nb = match self.native_build(
                    &mut ctx,
                    req,
                    r,
                    &tb,
                    &cand_src,
                    &cand_out,
                    &model_mods,
                ) {
                    Ok(b) => b,
                    Err(f) => {
                        build_failed(&mut findings, f);
                        break 'pipeline;
                    }
                };
                compiled.extend(need.iter().cloned());
                evidence.push(EvidenceRef {
                    label: "judge-built native verifier".into(),
                    digest: nb.digest.clone(),
                    public: true,
                });
                if let Some(c) = &r.candidate_binary_digest {
                    if c != &nb.digest {
                        findings.push(Finding::new(
                            ReasonCode::ArtifactBindingFailed,
                            Scope::Binding,
                            format!(
                                "candidate-supplied native verifier {c} is not the judge build of {} ({}); only judge-built binaries are admitted",
                                r.model_decl, nb.digest
                            ),
                        ));
                    }
                }
                extra.insert(
                    "bin_digest".to_string(),
                    crate::expected::LeanValue::Bytes(nb.digest.hex().to_string()),
                );
                extra.insert(
                    "toolchain_id".to_string(),
                    crate::expected::LeanValue::Str(r.toolchain_id.clone()),
                );
                native_build = Some(nb);
            }

            let expected_src = match req.expected.render_with(&extra) {
                Ok(s) => s,
                Err(e) => {
                    findings.push(Finding::unknown(
                        ReasonCode::InfraError,
                        format!("expected statement: {e}"),
                    ));
                    break 'pipeline;
                }
            };
            let reference = match self.reference(&mut ctx, req, &image, &tb, &expected_src) {
                Ok(r) => r,
                Err(f) => {
                    findings.push(f);
                    break 'pipeline;
                }
            };
            evidence.push(EvidenceRef {
                label: "reference export (ndjson)".into(),
                digest: reference.export_digest.clone(),
                public: true,
            });
            evidence.push(EvidenceRef {
                label: "expected statement source".into(),
                digest: reference.expected_source_digest.clone(),
                public: true,
            });
            statement_digest = Some(reference.expected_source_digest.clone());

            // A1 (native-lean): judge-generated instantiation of the statement at the model.
            let mut all_mods: Vec<CandidateModule> = Vec::new();
            if let Some(r) = model_route {
                let src =
                    native::render_inst(r, req.expected.module_name(), req.expected.decl_name());
                let rel = format!("{}.lean", r.inst_module.replace('.', "/"));
                let _ = std::fs::create_dir_all(cand_src.join(&rel).parent().unwrap());
                if let Err(e) = std::fs::write(cand_src.join(&rel), &src) {
                    findings.push(Finding::unknown(ReasonCode::InfraError, e.to_string()));
                    break 'pipeline;
                }
                let inst = CandidateModule {
                    name: r.inst_module.clone(),
                    rel_path: rel,
                    imports: vec![req.expected.module_name().into(), r.model_module.clone()],
                };
                if let Err(f) = compile(
                    &mut ctx,
                    "statement",
                    std::slice::from_ref(&inst),
                    &cand_src,
                    &cand_out,
                    Some(&reference.out),
                    &req.limits,
                    false,
                ) {
                    let detail = f.detail.clone();
                    findings.push(if f.severity == crate::findings::Severity::Unknown {
                        f
                    } else {
                        Finding::new(
                            shadow_or(&detail, ReasonCode::ArtifactBindingFailed),
                            Scope::All,
                            format!("statement cannot be instantiated at verifier model {} (missing, not an OracleVerifier, or redefining trusted names): {detail}", r.model_decl),
                        )
                    });
                    break 'pipeline;
                }
                compiled.insert(inst.name.clone());
                all_mods.push(inst);
            }
            let rest: Vec<CandidateModule> = staged
                .modules
                .iter()
                .filter(|m| !compiled.contains(&m.name))
                .cloned()
                .collect();
            if let Err(f) = compile(
                &mut ctx,
                "candidate",
                &rest,
                &cand_src,
                &cand_out,
                Some(&reference.out),
                &req.limits,
                false,
            ) {
                build_failed(&mut findings, f);
                break 'pipeline;
            }
            all_mods.extend(staged.modules.iter().cloned());
            let cand_mods: Vec<String> = all_mods.iter().map(|m| m.name.clone()).collect();

            // ---------------- Stage B: clean recheck on a fresh copy of the
            // candidate's .olean files only (nothing else the elaboration wrote).
            let replay = req.work_dir.join("replay");
            let replay_oleans = replay.join("oleans");
            let x = replay.join("x");
            let _ = std::fs::create_dir_all(&replay_oleans);
            let _ = std::fs::create_dir_all(&x);
            for m in &all_mods {
                let stem = m.rel_path.trim_end_matches(".lean");
                for suffix in [".olean", ".olean.server", ".olean.private"] {
                    let from = cand_out.join(format!("{stem}{suffix}"));
                    // Never follow links planted by the sandboxed build (they
                    // could point at host files): regular files only.
                    let regular = std::fs::symlink_metadata(&from)
                        .map(|m| m.file_type().is_file())
                        .unwrap_or(false);
                    if from.exists() && !regular {
                        findings.push(Finding::new(
                            ReasonCode::SandboxViolation,
                            Scope::All,
                            format!("build output {stem}{suffix} is not a regular file"),
                        ));
                        break 'pipeline;
                    }
                    if regular {
                        let to = replay_oleans.join(format!("{stem}{suffix}"));
                        let _ = std::fs::create_dir_all(to.parent().unwrap());
                        if let Err(e) = std::fs::copy(&from, &to) {
                            findings.push(Finding::unknown(
                                ReasonCode::InfraError,
                                format!("copy olean: {e}"),
                            ));
                            break 'pipeline;
                        }
                    }
                }
                if let Ok(d) = sha256_file(&replay_oleans.join(format!("{stem}.olean"))) {
                    evidence.push(EvidenceRef {
                        label: format!("candidate olean {}", m.name),
                        digest: d,
                        public: true,
                    });
                }
            }
            if let Err(e) = link_trusted(&reference.out, &replay_oleans) {
                findings.push(Finding::unknown(
                    ReasonCode::InfraError,
                    format!("link trusted: {e}"),
                ));
                break 'pipeline;
            }
            let lean_path = G_CAND.to_string();
            let mount_replay = |spec: &mut RunSpec| {
                spec.ro.push((reference.out.clone(), G_TRUSTED.into()));
                spec.ro.push((replay_oleans.clone(), G_CAND.into()));
            };

            // B1: leanchecker (Lean kernel replay of every candidate module),
            // in bounded batches of modules (see `Limits::recheck_batch_modules`).
            rechecks.push(module_rechecker(
                &mut ctx,
                "leanchecker",
                &format!("{G_TC}/bin/leanchecker"),
                &cand_mods,
                &lean_path,
                &req.limits,
                &mount_replay,
                &mut findings,
            ));

            // B2: export the certificate's closure (sandboxed: loads candidate oleans).
            let cand_export = x.join("candidate.ndjson");
            let export_ok = {
                let mut argv = vec![G_EXPORT.to_string()];
                argv.extend(cand_mods.iter().cloned());
                argv.push("--".into());
                argv.push(req.certificate.clone());
                let mut spec = ctx.base_spec(
                    argv,
                    &lean_path,
                    req.limits.recheck_timeout,
                    req.limits.mem_bytes,
                );
                mount_replay(&mut spec);
                spec.stdout_file = Some(cand_export.clone());
                spec.max_file_bytes = req.limits.export_max_bytes;
                match ctx.run("recheck:lean4export", &spec, CAPTURE_LIMIT) {
                    Err(f) => {
                        findings.push(f);
                        false
                    }
                    Ok(o) if o.exit == RunExit::TimedOut => {
                        findings.push(Finding::unknown(
                            ReasonCode::Timeout,
                            "lean4export timed out".into(),
                        ));
                        false
                    }
                    Ok(o) if !o.success() => {
                        warnings.push(format!(
                            "lean4export failed: {}",
                            lossy_tail(&o.stderr, 600)
                        ));
                        false
                    }
                    Ok(_) => true,
                }
            };
            if export_ok {
                if let Ok(d) = sha256_file(&cand_export) {
                    evidence.push(EvidenceRef {
                        label: "candidate certificate export (ndjson)".into(),
                        digest: d,
                        public: true,
                    });
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
                            RecheckerRun {
                                id: "nanoda".into(),
                                ran: false,
                                verdict: "error".into(),
                                wall_ms: 0,
                                detail: "infra".into(),
                            }
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
            // B4: lean4lean (independent kernel implementation, .olean replay),
            // batched like leanchecker.
            if self.tools.lean4lean.is_some() {
                rechecks.push(module_rechecker(
                    &mut ctx,
                    "lean4lean",
                    G_L4L,
                    &cand_mods,
                    &lean_path,
                    &req.limits,
                    &mount_replay,
                    &mut findings,
                ));
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
                    findings.push(Finding::unknown(
                        ReasonCode::InfraError,
                        format!("required rechecker {req_id} did not run"),
                    ));
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
                "modelDecl": model_route.map(|r| r.model_decl.clone()).unwrap_or_default(),
                "instDecl": model_route.map(|r| r.inst_decl.clone()).unwrap_or_default(),
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
                        findings.push(Finding::unknown(
                            ReasonCode::Timeout,
                            "arena-audit timed out".into(),
                        ));
                        None
                    }
                    Ok(o) => {
                        match serde_json::from_slice::<LeanAudit>(&o.stdout) {
                            Ok(a) if o.success() => {
                                let _ =
                                    std::fs::write(req.work_dir.join("lean-audit.json"), &o.stdout);
                                evidence.push(EvidenceRef {
                                    label: "arena-audit report".into(),
                                    digest: Digest::of_bytes(&o.stdout),
                                    public: true,
                                });
                                rechecks.push(RecheckerRun {
                                    id: "arena-audit".into(),
                                    ran: true,
                                    verdict: "completed".into(),
                                    wall_ms: o.wall.as_millis() as u64,
                                    detail: String::new(),
                                });
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
                        }
                    }
                }
            };
            let nd: Option<audit::NdAudit> = if export_ok {
                let t = Instant::now();
                match Export::read(&cand_export, req.limits.export_max_bytes) {
                    Ok(ex) => {
                        let n_conj = req.policy.conjunct_gates.as_ref().map_or(1, |c| c.len());
                        let nm = model_route.map(|r| audit::NdModel {
                            model_decl: &r.model_decl,
                            inst_decl: &r.inst_decl,
                        });
                        let a = audit::nd_audit(
                            &ex,
                            &reference.export,
                            &req.certificate,
                            req.expected.decl_name(),
                            n_conj,
                            nm,
                        );
                        if let Some(n) = nanoda_count {
                            if n == 0 || (ex.decls.len() as u64) < n / 2 {
                                findings.push(Finding::new(
                                    ReasonCode::RecheckFailed,
                                    Scope::All,
                                    format!(
                                        "nanoda checked {n} declarations but export has {}",
                                        ex.decls.len()
                                    ),
                                ));
                            }
                        }
                        ctx.timings.push(Timing {
                            step: "audit:ndjson".into(),
                            wall_ms: t.elapsed().as_millis() as u64,
                        });
                        rechecks.push(RecheckerRun {
                            id: "ndjson-audit".into(),
                            ran: true,
                            verdict: "completed".into(),
                            wall_ms: t.elapsed().as_millis() as u64,
                            detail: format!("{} decls", ex.decls.len()),
                        });
                        Some(a)
                    }
                    Err(e) => {
                        findings.push(Finding::new(
                            ReasonCode::RecheckFailed,
                            Scope::All,
                            format!("candidate export unreadable: {e}"),
                        ));
                        None
                    }
                }
            } else {
                None
            };
            let trusted_axioms = nd
                .as_ref()
                .map(|a| a.trusted_axioms.clone())
                .unwrap_or_else(|| {
                    reference
                        .export
                        .decls
                        .values()
                        .filter(|d| d.kind == crate::ndjson::DeclKind::Axiom)
                        .map(|d| d.name.clone())
                        .collect::<BTreeSet<_>>()
                });
            if let (Some(la), Some(r)) = (&lean_audit, model_route) {
                findings.extend(audit::lean_model_findings(
                    la,
                    &r.model_decl,
                    &r.model_module,
                    &req.policy.axiom_allowlist,
                    &trusted_axioms,
                ));
                model_report = Some(report::ModelReport {
                    decl: r.model_decl.clone(),
                    module: r.model_module.clone(),
                    closure_digest: nd.as_ref().and_then(|a| a.model_closure_digest.clone()),
                    axioms: la.model_axioms.clone(),
                });
            }
            if let Some(la) = &lean_audit {
                let per_conjunct = nd.as_ref().is_some_and(|a| a.conjunct_axioms.is_some());
                findings.extend(audit::lean_findings(
                    la,
                    &req.policy.axiom_allowlist,
                    &trusted_axioms,
                    per_conjunct,
                ));
            }
            if let Some(a) = &nd {
                findings.extend(audit::nd_findings(a, &req.policy.axiom_allowlist));
                graph_type_ok = a.type_equal;
                graph_axioms = a.axioms.iter().cloned().collect();
                if let Some(c) = a.closure_digest.clone() {
                    cert_digest = Some(c.clone());
                    let listing = serde_json::to_vec(&a.closure).unwrap_or_default();
                    let _ = std::fs::write(req.work_dir.join("closure.json"), &listing);
                    let lref = EvidenceRef {
                        label: "certificate dependency closure".into(),
                        digest: Digest::of_bytes(&listing),
                        public: true,
                    };
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
                let missing = lean_audit
                    .as_ref()
                    .is_some_and(|l| l.certificate_found != Some(true));
                if !missing {
                    findings.push(Finding::new(
                        ReasonCode::RecheckFailed,
                        Scope::All,
                        "certificate closure could not be exported for independent checking".into(),
                    ));
                }
            }
            if let (Some(la), Some(a)) = (&lean_audit, &nd) {
                if let Some(f) = audit::cross_check(la, a) {
                    findings.push(f);
                }
            }
            if lean_audit.is_none() && !report::has_fail(&findings) {
                findings.push(Finding::unknown(
                    ReasonCode::InfraError,
                    "Lean-side audit unavailable".into(),
                ));
            }
        }

        let mut findings = report::dedupe(findings);
        let finished = now_rfc3339();
        let mut gate_specs = req.policy.gates.clone();
        if !matches!(req.route, VerifierRoute::Standard)
            && !gate_specs
                .iter()
                .any(|g| g.gate == ObligationId::ArtifactBinding)
        {
            gate_specs.push(GateSpec {
                gate: ObligationId::ArtifactBinding,
                mandatory: true,
            });
        }
        if let (VerifierRoute::NativeLean(r), None) = (&req.route, &native_build) {
            if report::has_fail(&findings) {
                if !findings
                    .iter()
                    .any(|f| f.code == ReasonCode::ArtifactBindingFailed)
                {
                    findings.push(Finding::new(
                        ReasonCode::ArtifactBindingFailed,
                        Scope::Binding,
                        format!(
                            "no judge-built verifier: the model {} did not build",
                            r.model_decl
                        ),
                    ));
                }
            } else {
                findings.push(Finding::unknown(
                    ReasonCode::InfraError,
                    "native verifier was not built".into(),
                ));
            }
        }
        let gates = report::assemble_gates(
            &gate_specs,
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
            statement_digest: statement_digest.clone(),
            trusted: &trusted_list,
            axioms: &graph_axioms,
            allowlist: &req.policy.axiom_allowlist,
            rechecks: &rechecks,
            type_ok: graph_type_ok && !report::has_fail(&findings),
            evidence: evidence.iter().map(|e| e.digest.clone()).collect(),
            toolchain_digest: image.clone(),
            model: model_report.as_ref(),
            native: native_build.as_ref(),
            interp: match &req.route {
                VerifierRoute::Standard => req
                    .expected
                    .interp_verifier_digest()
                    .and_then(|h| Digest::try_from(format!("sha256:{h}")).ok()),
                _ => None,
            },
        });
        FormalCheckReport {
            schema: REPORT_SCHEMA,
            cache_key,
            lean_toolchain: lean_toolchain().into(),
            runner: self.runner.id().into(),
            tier_cap: self
                .runner
                .demo_only()
                .then_some(arena_types::challenge::Tier::Demo),
            gates,
            findings,
            rechecks,
            closure: closure_report,
            evidence,
            evidence_graph: graph,
            native_verifier: native_build,
            model: model_report,
            warnings,
            timings: ctx.timings,
        }
    }
}

/// Run a module-replaying rechecker (`leanchecker`, `lean4lean`) over the
/// candidate modules in sequential batches of `limits.recheck_batch_modules`
/// sandbox runs. Accepted only if every batch exits 0; the first failing
/// batch decides the verdict (later batches are not run). Exceeding
/// `limits.recheck_total` is a timeout (UNKNOWN), never an acceptance.
#[allow(clippy::too_many_arguments)]
fn module_rechecker(
    ctx: &mut Ctx<'_>,
    id: &str,
    tool: &str,
    mods: &[String],
    lean_path: &str,
    limits: &Limits,
    mount: &dyn Fn(&mut RunSpec),
    findings: &mut Vec<Finding>,
) -> RecheckerRun {
    let batch = limits.recheck_batch_modules.max(1);
    let started = Instant::now();
    let mut wall_ms = 0u64;
    let chunks: Vec<&[String]> = if mods.is_empty() {
        vec![&[][..]]
    } else {
        mods.chunks(batch).collect()
    };
    let n = chunks.len();
    for (i, chunk) in chunks.into_iter().enumerate() {
        if started.elapsed() > limits.recheck_total {
            findings.push(Finding::unknown(
                ReasonCode::Timeout,
                format!("{id} exceeded its total budget after {i} of {n} batches"),
            ));
            return RecheckerRun {
                id: id.into(),
                ran: true,
                verdict: "timeout".into(),
                wall_ms,
                detail: format!("{i}/{n} batches"),
            };
        }
        let mut argv = vec![tool.to_string()];
        argv.extend(chunk.iter().cloned());
        let mut spec = ctx.base_spec(argv, lean_path, limits.recheck_timeout, limits.mem_bytes);
        mount(&mut spec);
        let step = if n == 1 {
            format!("recheck:{id}")
        } else {
            format!("recheck:{id}:{}", chunk.join(","))
        };
        match ctx.run(&step, &spec, CAPTURE_LIMIT) {
            Err(f) => {
                findings.push(f);
                return RecheckerRun {
                    id: id.into(),
                    ran: false,
                    verdict: "error".into(),
                    wall_ms,
                    detail: "infra".into(),
                };
            }
            Ok(o) => {
                wall_ms += o.wall.as_millis() as u64;
                if !o.success() {
                    let mut r = verdict(id, &o, findings);
                    r.wall_ms = wall_ms;
                    if n > 1 {
                        r.detail = format!(
                            "batch {} of {n} ({}): {}",
                            i + 1,
                            chunk.join(", "),
                            r.detail
                        );
                    }
                    return r;
                }
            }
        }
    }
    RecheckerRun {
        id: id.into(),
        ran: true,
        verdict: "accepted".into(),
        wall_ms,
        detail: if n > 1 {
            format!("{} modules in {n} runs", mods.len())
        } else {
            String::new()
        },
    }
}

fn verdict(id: &str, o: &RunOutcome, findings: &mut Vec<Finding>) -> RecheckerRun {
    let wall_ms = o.wall.as_millis() as u64;
    let (v, detail) = match &o.exit {
        RunExit::Exited(0) => ("accepted", String::new()),
        RunExit::TimedOut => {
            findings.push(Finding::unknown(
                ReasonCode::Timeout,
                format!("{id} timed out"),
            ));
            ("timeout", String::new())
        }
        other => {
            let d = format!(
                "{other:?}: {}{}",
                lossy_tail(&o.stdout, 400),
                lossy_tail(&o.stderr, 800)
            );
            findings.push(Finding::new(
                ReasonCode::RecheckFailed,
                Scope::All,
                format!("{id} rejected the candidate environment: {d}"),
            ));
            ("rejected", d)
        }
    };
    RecheckerRun {
        id: id.into(),
        ran: true,
        verdict: v.into(),
        wall_ms,
        detail: crate::findings::bound(detail),
    }
}
