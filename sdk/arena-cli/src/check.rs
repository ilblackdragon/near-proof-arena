//! `arena check-local`: the judge's cheap gates, approximated locally.
//!
//! LOCAL CHECK — NOT AN OFFICIAL VERDICT. Formal gates are not run (only a
//! lexical heuristic), timings are from this machine, and the sandbox is a
//! best-effort `unshare` network namespace, not the judge's microVM.

use crate::archive::{self, ArchiveError, ArchiveLimits, ValidatedPackage};
use crate::exit::{CliError, CliResult};
use crate::pack;
use crate::proc::{ExitKind, Outcome, Runner};
use arena_types::{CandidateManifest, ChallengeDefinition, Digest, ObligationId, ReasonCode};
use serde::Serialize;
use std::collections::BTreeMap;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

pub const BANNER: &str = "LOCAL CHECK — NOT AN OFFICIAL VERDICT";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum LocalStatus {
    Pass,
    Fail,
    Warn,
    Skipped,
}

#[derive(Clone, Debug, Serialize)]
pub struct LocalGate {
    /// Judge gate this approximates.
    pub gate: ObligationId,
    pub status: LocalStatus,
    pub reason_codes: Vec<ReasonCode>,
    pub details: Vec<String>,
}

impl LocalGate {
    fn new(gate: ObligationId) -> Self {
        LocalGate {
            gate,
            status: LocalStatus::Pass,
            reason_codes: vec![],
            details: vec![],
        }
    }
    fn fail(&mut self, rc: ReasonCode, msg: impl Into<String>) {
        self.status = LocalStatus::Fail;
        if !self.reason_codes.contains(&rc) {
            self.reason_codes.push(rc);
        }
        self.details.push(msg.into());
    }
    fn warn(&mut self, rc: Option<ReasonCode>, msg: impl Into<String>) {
        if self.status == LocalStatus::Pass {
            self.status = LocalStatus::Warn;
        }
        if let Some(rc) = rc {
            if !self.reason_codes.contains(&rc) {
                self.reason_codes.push(rc);
            }
        }
        self.details.push(msg.into());
    }
    fn skip(gate: ObligationId, msg: impl Into<String>) -> Self {
        LocalGate {
            gate,
            status: LocalStatus::Skipped,
            reason_codes: vec![],
            details: vec![msg.into()],
        }
    }
    fn note(&mut self, msg: impl Into<String>) {
        self.details.push(msg.into());
    }
}

#[derive(Debug, Serialize)]
pub struct LocalReport {
    pub official: bool,
    pub banner: &'static str,
    pub challenge_id: String,
    pub package_digest: Option<Digest>,
    pub network_isolated: bool,
    pub gates: Vec<LocalGate>,
    pub ok: bool,
}

#[derive(Debug, Clone)]
pub struct CheckOptions {
    pub challenge: String,
    pub challenge_file: Option<PathBuf>,
    pub fixtures: Option<PathBuf>,
    pub skip_build: bool,
    pub no_repro: bool,
    pub allow_network: bool,
    pub keep: bool,
    /// Archive format to pack and validate (same as `submit` would upload).
    pub format: pack::Format,
}

/// Manifest + layout + challenge-consistency checks on a directory (no build).
/// Returns the PKG_WELLFORMED gate and the validated package (if it packed).
pub fn check_package(
    dir: &Path,
    opts: &CheckOptions,
    chal: Option<&ChallengeDefinition>,
) -> (LocalGate, Option<(Vec<u8>, ValidatedPackage)>) {
    let mut g = LocalGate::new(ObligationId::PkgWellformed);
    let mpath = dir.join("candidate.toml");
    let src = match std::fs::read_to_string(&mpath) {
        Ok(s) => s,
        Err(e) => {
            g.fail(
                ReasonCode::ManifestInvalid,
                format!("cannot read {}: {e}", mpath.display()),
            );
            return (g, None);
        }
    };
    let manifest = match CandidateManifest::parse(&src) {
        Ok(m) => m,
        Err(e) => {
            g.fail(ReasonCode::ManifestInvalid, format!("candidate.toml: {e}"));
            return (g, None);
        }
    };
    check_manifest_semantics(dir, &manifest, opts, chal, &mut g);

    // Pack exactly as `arena pack`/`arena submit` would, then re-validate the
    // archive bytes with the archive safety rules.
    let bytes = match pack::pack(dir, opts.format) {
        Ok(b) => b,
        Err(e) => {
            g.fail(ReasonCode::ArchiveUnsafe, e.msg);
            return (g, None);
        }
    };
    match archive::validate_package(&bytes, &ArchiveLimits::default(), None) {
        Ok(v) => {
            g.note(format!(
                "package {} ({} files, {} bytes packed, {} bytes expanded)",
                v.package_digest,
                v.files.len(),
                v.compressed_bytes,
                v.expanded_bytes
            ));
            if v.manifest != manifest {
                g.fail(
                    ReasonCode::ManifestInvalid,
                    "manifest in archive differs from candidate.toml on disk",
                );
            }
            let st = g.status;
            if st == LocalStatus::Fail {
                return (g, None);
            }
            (g, Some((bytes, v)))
        }
        Err(ArchiveError::Unsafe(m)) => {
            g.fail(ReasonCode::ArchiveUnsafe, m);
            (g, None)
        }
        Err(ArchiveError::Manifest(m)) => {
            g.fail(ReasonCode::ManifestInvalid, m);
            (g, None)
        }
    }
}

fn check_manifest_semantics(
    dir: &Path,
    m: &CandidateManifest,
    opts: &CheckOptions,
    chal: Option<&ChallengeDefinition>,
    g: &mut LocalGate,
) {
    if m.challenge != opts.challenge {
        g.fail(
            ReasonCode::ManifestInvalid,
            format!(
                "candidate.toml challenge = {:?} but --challenge {}",
                m.challenge, opts.challenge
            ),
        );
    }
    for d in ["source", "dependency-locks", "build-recipe"] {
        if !dir.join(d).is_dir() {
            g.fail(
                ReasonCode::ManifestInvalid,
                format!("required directory {d}/ is missing"),
            );
        }
    }
    if !dir.join("README.md").is_file() {
        g.fail(ReasonCode::ManifestInvalid, "README.md is missing");
    }
    let recipe = dir.join(&m.build.recipe);
    if !recipe.is_file() {
        g.fail(
            ReasonCode::ManifestInvalid,
            format!("build recipe {} not found", m.build.recipe),
        );
    }
    for (role, p) in [
        ("prepare", &m.entry.prepare),
        ("prove", &m.entry.prove),
        ("verify", &m.entry.verify),
    ] {
        if !m.build.outputs.contains(p) {
            g.fail(
                ReasonCode::ManifestInvalid,
                format!("entry.{role} = {p:?} is not listed in build.outputs"),
            );
        }
    }
    match &m.formal {
        Some(f) => {
            if !dir.join(&f.lean_project).is_dir() {
                g.fail(
                    ReasonCode::CertificateMissing,
                    format!("formal.lean_project {}/ is missing", f.lean_project),
                );
            }
        }
        None => {
            if chal
                .map(|c| c.tier == arena_types::challenge::Tier::Formal)
                .unwrap_or(true)
            {
                g.warn(
                    Some(ReasonCode::CertificateMissing),
                    "no [formal] section: formal-tier challenges will reject with CERTIFICATE_MISSING",
                );
            }
        }
    }
    if let Some(c) = chal {
        // v1.7: declared_tier is required iff the challenge has coverage tiers.
        if let Err(e) = c.declared_tier(m) {
            g.fail(ReasonCode::ManifestInvalid, e);
        }
        if m.security_profile_request != c.security_profile.id {
            g.fail(
                ReasonCode::ProfileNotAllowed,
                format!(
                    "security_profile_request {:?} != challenge profile {:?}",
                    m.security_profile_request, c.security_profile.id
                ),
            );
        }
        if m.hardware.gpu && c.hardware_profile.gpu.is_none() {
            g.fail(
                ReasonCode::ManifestInvalid,
                format!(
                    "candidate requests a GPU but hardware profile {} has none",
                    c.hardware_profile.id
                ),
            );
        }
        if (m.hardware.min_ram_gb as u64) << 30 > c.hardware_profile.ram_bytes {
            g.fail(
                ReasonCode::ManifestInvalid,
                format!(
                    "min_ram_gb {} exceeds hardware profile RAM",
                    m.hardware.min_ram_gb
                ),
            );
        }
    }
}

/// Load and authenticate a challenge definition file against the expected id.
pub fn load_challenge(path: &Path, expected_id: &str) -> CliResult<ChallengeDefinition> {
    let s = std::fs::read_to_string(path)?;
    let v: serde_json::Value = serde_json::from_str(&s)
        .map_err(|e| CliError::local(format!("{}: {e}", path.display())))?;
    // Accept either a bare definition or the API's `{id, definition}` envelope.
    let def_v = v.get("definition").cloned().unwrap_or(v);
    let def: ChallengeDefinition = serde_json::from_value(def_v).map_err(|e| {
        CliError::local(format!(
            "{}: not a ChallengeDefinition: {e}",
            path.display()
        ))
    })?;
    let id = def.id().map_err(|e| CliError::local(e.to_string()))?;
    if id != expected_id {
        return Err(CliError::local(format!(
            "CHALLENGE_UNKNOWN: {} hashes to {id}, not {expected_id}",
            path.display()
        )));
    }
    Ok(def)
}

/// Lexical scan of the Lean project for constructs the axiom audit rejects.
/// Heuristic only: the real gate elaborates and audits the kernel terms.
fn formal_heuristic(dir: &Path, m: &CandidateManifest) -> LocalGate {
    let mut g = LocalGate::new(ObligationId::AxiomAudit);
    let Some(f) = &m.formal else {
        return LocalGate::skip(ObligationId::AxiomAudit, "no [formal] section");
    };
    let mut files = Vec::new();
    collect_lean(&dir.join(&f.lean_project), &mut files);
    let patterns: &[(&str, ReasonCode)] = &[
        ("sorry", ReasonCode::SorryFound),
        ("admit", ReasonCode::SorryFound),
        ("native_decide", ReasonCode::NativeEvalFound),
        ("implemented_by", ReasonCode::NativeEvalFound),
        ("extern", ReasonCode::NativeEvalFound),
        ("axiom", ReasonCode::ForbiddenAxiom),
    ];
    for p in &files {
        let Ok(text) = std::fs::read_to_string(p) else {
            continue;
        };
        let text = strip_lean_comments(&text);
        for (lineno, code) in text.lines().enumerate() {
            for (pat, rc) in patterns {
                if code
                    .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                    .any(|w| w == *pat)
                {
                    g.warn(
                        Some(*rc),
                        format!(
                            "{}:{}: `{pat}`",
                            p.strip_prefix(dir).unwrap_or(p).display(),
                            lineno + 1
                        ),
                    );
                }
            }
        }
    }
    if g.status == LocalStatus::Pass {
        g.status = LocalStatus::Skipped;
        g.note(format!("formal gates are not run locally; lexical scan of {} .lean files found no sorry/admit/native_decide/extern/axiom", files.len()));
    }
    g.note("the judge elaborates the certificate in a clean checker image, checks the theorem type, audits transitive axioms and re-checks with independent kernels");
    g
}

/// Remove `-- line` and nested `/- block -/` comments, preserving newlines so
/// line numbers stay correct.
pub fn strip_lean_comments(src: &str) -> String {
    let b: Vec<char> = src.chars().collect();
    let mut out = String::with_capacity(src.len());
    let (mut i, mut depth) = (0usize, 0usize);
    while i < b.len() {
        let next = b.get(i + 1).copied();
        if depth > 0 {
            if b[i] == '/' && next == Some('-') {
                depth += 1;
                i += 2;
            } else if b[i] == '-' && next == Some('/') {
                depth -= 1;
                i += 2;
            } else {
                if b[i] == '\n' {
                    out.push('\n');
                }
                i += 1;
            }
        } else if b[i] == '/' && next == Some('-') {
            depth = 1;
            i += 2;
        } else if b[i] == '-' && next == Some('-') {
            while i < b.len() && b[i] != '\n' {
                i += 1;
            }
        } else {
            out.push(b[i]);
            i += 1;
        }
    }
    out
}

fn collect_lean(d: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(d) else { return };
    let mut ents: Vec<_> = rd.flatten().collect();
    ents.sort_by_key(|e| e.file_name());
    for e in ents {
        let p = e.path();
        let name = e.file_name();
        if p.is_dir() {
            if name != ".lake" {
                collect_lean(&p, out);
            }
        } else if p.extension().map(|x| x == "lean").unwrap_or(false) {
            out.push(p);
        }
    }
}

fn ms(limit: Option<u64>, default_ms: u64) -> Duration {
    Duration::from_millis(limit.unwrap_or(default_ms))
}

fn dir_digest_and_size(d: &Path) -> (BTreeMap<String, Digest>, u64) {
    let mut m = BTreeMap::new();
    let mut total = 0;
    fn rec(root: &Path, d: &Path, m: &mut BTreeMap<String, Digest>, total: &mut u64) {
        let Ok(rd) = std::fs::read_dir(d) else { return };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                rec(root, &p, m, total);
            } else if let Ok(b) = std::fs::read(&p) {
                *total += b.len() as u64;
                m.insert(
                    p.strip_prefix(root).unwrap().to_string_lossy().into_owned(),
                    Digest::of_bytes(&b),
                );
            }
        }
    }
    rec(d, d, &mut m, &mut total);
    (m, total)
}

fn set_readonly(p: &Path, ro: bool) {
    let Ok(md) = std::fs::symlink_metadata(p) else {
        return;
    };
    if md.is_dir() {
        if let Ok(rd) = std::fs::read_dir(p) {
            for e in rd.flatten() {
                set_readonly(&e.path(), ro);
            }
        }
    }
    let mut mode = md.permissions().mode();
    if ro {
        mode &= !0o222;
    } else {
        mode |= 0o200;
    }
    let _ = std::fs::set_permissions(p, std::fs::Permissions::from_mode(mode));
}

struct Work {
    root: Option<tempfile::TempDir>,
    keep: bool,
}

impl Work {
    fn path(&self) -> &Path {
        self.root.as_ref().expect("work dir").path()
    }
}

impl Drop for Work {
    fn drop(&mut self) {
        if let Some(root) = self.root.take() {
            set_readonly(root.path(), false);
            if self.keep {
                eprintln!("kept work dir: {}", root.keep().display());
            }
        }
    }
}

fn fresh_dir(base: &Path, name: &str) -> PathBuf {
    let p = base.join(name);
    let _ = std::fs::create_dir_all(&p);
    p
}

/// Build in `pkg_dir` (an extracted package). Returns output digests.
fn build_once(
    runner: &Runner,
    pkg_dir: &Path,
    home: &Path,
    m: &CandidateManifest,
    timeout: Duration,
) -> Result<BTreeMap<String, Digest>, (ReasonCode, String)> {
    let argv = vec!["bash".to_string(), m.build.recipe.clone()];
    let o = runner.run(
        &argv,
        pkg_dir,
        home,
        &[("ARENA_BUILD", "1".into())],
        timeout,
    );
    match o.exit {
        ExitKind::Exited(0) => {}
        ExitKind::TimedOut => {
            return Err((
                ReasonCode::Timeout,
                format!("build timed out after {timeout:?}"),
            ))
        }
        _ => {
            return Err((
                ReasonCode::BuildFailed,
                format!("build recipe {}:\n{}", o.describe(), o.tail()),
            ))
        }
    }
    let mut out = BTreeMap::new();
    for p in &m.build.outputs {
        let f = pkg_dir.join(p);
        match std::fs::read(&f) {
            Ok(b) => {
                out.insert(p.clone(), Digest::of_bytes(&b));
            }
            Err(_) => {
                return Err((
                    ReasonCode::BuildFailed,
                    format!("declared output {p} was not produced"),
                ))
            }
        }
    }
    for e in [&m.entry.prepare, &m.entry.prove, &m.entry.verify] {
        let md = std::fs::metadata(pkg_dir.join(e))
            .map_err(|err| (ReasonCode::BuildFailed, format!("{e}: {err}")))?;
        if md.permissions().mode() & 0o111 == 0 {
            return Err((
                ReasonCode::BuildFailed,
                format!("entry point {e} is not executable"),
            ));
        }
    }
    Ok(out)
}

#[derive(Debug)]
struct Case {
    name: String,
    request: PathBuf,
    witness: PathBuf,
    expected_claim: Option<PathBuf>,
}

fn load_fixtures(dir: &Path) -> CliResult<(Option<PathBuf>, Vec<Case>)> {
    // Entry points run with their scratch dir as cwd: use absolute paths.
    let dir = &std::path::absolute(dir)
        .map_err(|e| CliError::local(format!("fixtures {}: {e}", dir.display())))?;
    let params = dir.join("params.bin");
    let params = params.is_file().then_some(params);
    let cases_dir = dir.join("cases");
    let mut cases = Vec::new();
    let rd = std::fs::read_dir(&cases_dir)
        .map_err(|e| CliError::local(format!("fixtures {}: {e}", cases_dir.display())))?;
    let mut names: Vec<_> = rd
        .flatten()
        .filter(|e| e.path().is_dir())
        .map(|e| e.file_name())
        .collect();
    names.sort();
    for n in names {
        let c = cases_dir.join(&n);
        let request = c.join("request.bin");
        let witness = c.join("witness.bin");
        if !request.is_file() || !witness.is_file() {
            return Err(CliError::local(format!(
                "fixture {} lacks request.bin/witness.bin",
                c.display()
            )));
        }
        let ec = c.join("expected_claim.bin");
        cases.push(Case {
            name: n.to_string_lossy().into_owned(),
            request,
            witness,
            expected_claim: ec.is_file().then_some(ec),
        });
    }
    Ok((params, cases))
}

fn hostile_variants(proof: &[u8]) -> Vec<(&'static str, Vec<u8>)> {
    let mut v = Vec::new();
    if !proof.is_empty() {
        let mut a = proof.to_vec();
        a[0] ^= 0x01;
        v.push(("first byte flipped", a));
        let mut b = proof.to_vec();
        let l = b.len() - 1;
        b[l] ^= 0x80;
        v.push(("last byte flipped", b));
        let mut m = proof.to_vec();
        let mid = m.len() / 2;
        m[mid] ^= 0xff;
        v.push(("middle byte inverted", m));
        v.push(("truncated to half", proof[..proof.len() / 2].to_vec()));
    }
    v.push(("empty proof", Vec::new()));
    let mut ext = proof.to_vec();
    ext.push(0);
    v.push(("trailing byte appended", ext));
    v
}

/// Full local check. Prints nothing; the caller renders the report.
pub fn run(dir: &Path, opts: &CheckOptions) -> CliResult<LocalReport> {
    let chal = match &opts.challenge_file {
        Some(p) => Some(load_challenge(p, &opts.challenge)?),
        None => None,
    };
    let runner = Runner::detect(opts.allow_network);
    let mut gates = Vec::new();
    let (pkg_gate, pkg) = check_package(dir, opts, chal.as_ref());
    let package_digest = pkg.as_ref().map(|(_, v)| v.package_digest.clone());
    gates.push(pkg_gate);
    let finish = |gates: Vec<LocalGate>, package_digest| {
        let ok = gates.iter().all(|g| g.status != LocalStatus::Fail);
        Ok(LocalReport {
            official: false,
            banner: BANNER,
            challenge_id: opts.challenge.clone(),
            package_digest,
            network_isolated: runner.network_isolated(),
            gates,
            ok,
        })
    };
    let Some((bytes, validated)) = pkg else {
        return finish(gates, package_digest);
    };
    let m = validated.manifest.clone();
    gates.push(formal_heuristic(dir, &m));
    if opts.skip_build {
        gates.push(LocalGate::skip(
            ObligationId::BuildReproducible,
            "--skip-build",
        ));
        return finish(gates, package_digest);
    }

    let limits = chal.as_ref().map(|c| c.resource_limits.clone());
    // v1.7: on a coverage-tiered challenge `prove` exit 3 is UNSUPPORTED (an
    // abstention, not a failure; local fixtures carry no class, so no
    // COVERAGE_GAP_IN_TIER is decided here).
    let coverage_tiered = chal.as_ref().is_some_and(|c| c.coverage.is_some());
    let work = Work {
        root: Some(tempfile::Builder::new().prefix("arena-check-").tempdir()?),
        keep: opts.keep,
    };
    let home = fresh_dir(work.path(), "home");
    let pkg_dir = work.path().join("pkg");

    // --- BUILD_REPRODUCIBLE: build from the *packed archive*, twice, same path.
    let mut bg = LocalGate::new(ObligationId::BuildReproducible);
    if !runner.network_isolated() {
        bg.warn(None, "network isolation unavailable (unshare -r -n failed) or disabled; the judge builds with NO network");
    }
    let build_timeout = ms(limits.as_ref().map(|l| l.max_build_ms), 30 * 60 * 1000);
    let extract = |d: &Path| -> CliResult<()> {
        if d.exists() {
            set_readonly(d, false);
            std::fs::remove_dir_all(d)?;
        }
        std::fs::create_dir_all(d)?;
        archive::validate_package(&bytes, &ArchiveLimits::default(), Some(d))
            .map_err(|e| CliError::local(e.to_string()))?;
        Ok(())
    };
    extract(&pkg_dir)?;
    let first = build_once(&runner, &pkg_dir, &home, &m, build_timeout);
    let outputs = match first {
        Err((rc, msg)) => {
            bg.fail(rc, msg);
            gates.push(bg);
            return finish(gates, package_digest);
        }
        Ok(o) => o,
    };
    for (p, d) in &outputs {
        bg.note(format!("{p} {d}"));
    }
    if opts.no_repro {
        bg.warn(
            None,
            "--no-repro: second build skipped (the judge always builds twice)",
        );
    } else {
        extract(&pkg_dir)?;
        let home2 = fresh_dir(work.path(), "home2");
        match build_once(&runner, &pkg_dir, &home2, &m, build_timeout) {
            Err((rc, msg)) => bg.fail(rc, format!("second build: {msg}")),
            Ok(o2) => {
                for (p, d) in &outputs {
                    if o2.get(p) != Some(d) {
                        bg.fail(
                            ReasonCode::BuildNotReproducible,
                            format!(
                                "{p}: {d} vs {}",
                                o2.get(p).map(|d| d.to_string()).unwrap_or_default()
                            ),
                        );
                    }
                }
            }
        }
    }
    let build_failed = bg.status == LocalStatus::Fail;
    gates.push(bg);
    if build_failed {
        return finish(gates, package_digest);
    }

    // --- Process interface on public dev fixtures.
    let fixtures = opts
        .fixtures
        .clone()
        .or_else(|| std::env::var_os("ARENA_FIXTURES").map(PathBuf::from));
    let Some(fdir) = fixtures else {
        for g in [
            ObligationId::ConformanceDifferential,
            ObligationId::ProverReliability,
            ObligationId::AdversarialProofs,
            ObligationId::ResourceLimits,
        ] {
            gates.push(LocalGate::skip(
                g,
                "no public dev fixtures (pass --fixtures DIR or set ARENA_FIXTURES)",
            ));
        }
        return finish(gates, package_digest);
    };
    let (params, cases) = load_fixtures(&fdir)?;
    set_readonly(&pkg_dir, true);
    let entry = |e: &str| pkg_dir.join(e).to_string_lossy().into_owned();
    let s = |p: &Path| p.to_string_lossy().into_owned();

    let mut conf = LocalGate::new(ObligationId::ConformanceDifferential);
    let mut rel = LocalGate::new(ObligationId::ProverReliability);
    let mut adv = LocalGate::new(ObligationId::AdversarialProofs);
    let mut res = LocalGate::new(ObligationId::ResourceLimits);
    res.note("timings are from this machine and are informational only");

    // prepare (judge-run; its output is frozen and is the only state shared
    // between invocations).
    let params_path = match params {
        Some(p) => p,
        None => {
            let p = work.path().join("params.bin");
            std::fs::write(&p, b"")?;
            p
        }
    };
    let public = fresh_dir(work.path(), "public");
    let scratch = fresh_dir(work.path(), "prepare-scratch");
    let o = runner.run(
        &[
            entry(&m.entry.prepare),
            "--params".into(),
            s(&params_path),
            "--out".into(),
            s(&public),
        ],
        &scratch,
        &scratch,
        &[],
        ms(limits.as_ref().map(|l| l.max_prepare_ms), 10 * 60 * 1000),
    );
    if o.code() != Some(0) {
        rel.fail(
            if o.exit == ExitKind::TimedOut {
                ReasonCode::Timeout
            } else {
                ReasonCode::ProverFailed
            },
            format!("prepare: {}\n{}", o.describe(), o.tail()),
        );
        gates.extend([conf, rel]);
        gates.push(LocalGate::skip(
            ObligationId::AdversarialProofs,
            "prepare failed",
        ));
        gates.push(res);
        return finish(gates, package_digest);
    }
    let (public_digests, public_bytes) = dir_digest_and_size(&public);
    res.note(format!(
        "prepare: {:?}, public_dir {} files / {} bytes",
        o.wall,
        public_digests.len(),
        public_bytes
    ));
    if let Some(l) = &limits {
        if public_bytes > l.max_public_artifact_bytes {
            res.fail(
                ReasonCode::ResourceLimit,
                format!(
                    "public_dir {public_bytes} bytes > max_public_artifact_bytes {}",
                    l.max_public_artifact_bytes
                ),
            );
        }
    }
    set_readonly(&public, true);

    let verify_timeout = ms(limits.as_ref().map(|l| l.max_verify_ms), 60_000);
    let verify = |claim: &[u8], proof: &[u8], tag: &str| -> CliResult<Outcome> {
        let d = fresh_dir(work.path(), &format!("verify-{tag}"));
        let inp = fresh_dir(&d, "in");
        std::fs::write(inp.join("claim.bin"), claim)?;
        std::fs::write(inp.join("proof.bin"), proof)?;
        set_readonly(&inp, true);
        Ok(runner.run(
            &[
                entry(&m.entry.verify),
                "--public".into(),
                s(&public),
                "--claim".into(),
                s(&inp.join("claim.bin")),
                "--proof".into(),
                s(&inp.join("proof.bin")),
            ],
            &d,
            &d,
            &[],
            verify_timeout,
        ))
    };

    let mut honest: Vec<(String, Vec<u8>, Vec<u8>)> = Vec::new();
    for (i, c) in cases.iter().enumerate() {
        let d = fresh_dir(work.path(), &format!("prove-{i}"));
        let inp = fresh_dir(&d, "in");
        let outp = fresh_dir(&d, "out");
        std::fs::copy(&c.request, inp.join("request.bin"))?;
        std::fs::copy(&c.witness, inp.join("witness.bin"))?;
        set_readonly(&inp, true);
        let o = runner.run(
            &[
                entry(&m.entry.prove),
                "--public".into(),
                s(&public),
                "--request".into(),
                s(&inp.join("request.bin")),
                "--witness".into(),
                s(&inp.join("witness.bin")),
                "--claim-out".into(),
                s(&outp.join("claim.bin")),
                "--proof-out".into(),
                s(&outp.join("proof.bin")),
            ],
            &d,
            &d,
            &[],
            ms(limits.as_ref().map(|l| l.max_prove_ms), 10 * 60 * 1000),
        );
        if coverage_tiered && o.code() == Some(arena_types::coverage::PROVE_EXIT_UNSUPPORTED) {
            rel.note(format!(
                "{}: prove answered UNSUPPORTED (abstained)",
                c.name
            ));
            continue;
        }
        if o.code() != Some(0) {
            let rc = if o.exit == ExitKind::TimedOut {
                ReasonCode::Timeout
            } else {
                ReasonCode::ProverFailed
            };
            rel.fail(
                rc,
                format!("{}: prove {}\n{}", c.name, o.describe(), o.tail()),
            );
            continue;
        }
        let (claim, proof) = match (
            std::fs::read(outp.join("claim.bin")),
            std::fs::read(outp.join("proof.bin")),
        ) {
            (Ok(a), Ok(b)) => (a, b),
            _ => {
                rel.fail(
                    ReasonCode::ProverFailed,
                    format!("{}: prove exited 0 but did not write claim/proof", c.name),
                );
                continue;
            }
        };
        res.note(format!(
            "{}: prove {:?}, proof {} bytes",
            c.name,
            o.wall,
            proof.len()
        ));
        if dir_digest_and_size(&public).0 != public_digests {
            rel.fail(
                ReasonCode::SandboxViolation,
                format!("{}: prove modified public_dir", c.name),
            );
        }
        if let Some(l) = &limits {
            if proof.len() as u64 > l.max_proof_bytes {
                res.fail(
                    ReasonCode::ResourceLimit,
                    format!(
                        "{}: proof {} bytes > max_proof_bytes {}",
                        c.name,
                        proof.len(),
                        l.max_proof_bytes
                    ),
                );
            }
            if o.wall > Duration::from_millis(l.max_prove_ms) {
                res.warn(
                    Some(ReasonCode::ResourceLimit),
                    format!("{}: prove took {:?} > max_prove_ms locally", c.name, o.wall),
                );
            }
        }
        if let Some(c2) = &chal {
            if claim.len() as u64 > c2.claim_encoding.max_claim_bytes {
                conf.fail(
                    ReasonCode::ClaimMismatch,
                    format!("{}: claim {} bytes > max_claim_bytes", c.name, claim.len()),
                );
            }
        }
        match &c.expected_claim {
            Some(p) => {
                if std::fs::read(p)? != claim {
                    conf.fail(
                        ReasonCode::ClaimMismatch,
                        format!("{}: claim.bin != expected_claim.bin", c.name),
                    );
                }
            }
            None => conf.warn(
                None,
                format!("{}: no expected_claim.bin; claim not compared", c.name),
            ),
        }
        // honest verify, twice (determinism)
        let v1 = verify(&claim, &proof, &format!("{i}-a"))?;
        let v2 = verify(&claim, &proof, &format!("{i}-b"))?;
        res.note(format!("{}: verify {:?}", c.name, v1.wall));
        if v1.code() != Some(0) {
            rel.fail(
                ReasonCode::ProverFailed,
                format!(
                    "{}: verify rejected the honest proof ({})\n{}",
                    c.name,
                    v1.describe(),
                    v1.tail()
                ),
            );
        }
        if v1.code() != v2.code() {
            adv.fail(
                ReasonCode::VerifierNondeterministic,
                format!(
                    "{}: verify gave {} then {}",
                    c.name,
                    v1.describe(),
                    v2.describe()
                ),
            );
        }
        if let Some(l) = &limits {
            if v1.wall > Duration::from_millis(l.max_verify_ms) {
                res.warn(
                    Some(ReasonCode::ResourceLimit),
                    format!(
                        "{}: verify took {:?} > max_verify_ms locally",
                        c.name, v1.wall
                    ),
                );
            }
        }
        honest.push((c.name.clone(), claim, proof));
    }
    if cases.is_empty() {
        conf.warn(None, format!("{} contains no cases", fdir.display()));
    }

    // ADVERSARIAL_PROOFS: mutated proofs, mutated claims, cross-case proofs.
    for (ci, (name, claim, proof)) in honest.iter().enumerate() {
        let mut attempts: Vec<(String, Vec<u8>, Vec<u8>)> = hostile_variants(proof)
            .into_iter()
            .map(|(what, p)| (what.to_string(), claim.clone(), p))
            .collect();
        if !claim.is_empty() {
            let mut c2 = claim.clone();
            let l = c2.len() - 1;
            c2[l] ^= 0x01;
            attempts.push(("claim last byte flipped".into(), c2, proof.clone()));
        }
        for (oname, oclaim, oproof) in &honest {
            // A byte-identical proof is this case's own honest proof (e.g. two
            // requests with the same witness): accepting it is not hostile.
            if oname != name && oclaim != claim && oproof != proof {
                attempts.push((format!("proof of {oname}"), claim.clone(), oproof.clone()));
                break;
            }
        }
        for (k, (what, c, p)) in attempts.iter().enumerate() {
            let o = verify(c, p, &format!("adv-{ci}-{k}"))?;
            match o.code() {
                Some(1) => {}
                Some(0) => adv.fail(ReasonCode::HostileProofAccepted, format!("{name}: verify ACCEPTED hostile input ({what})")),
                _ => adv.warn(None, format!("{name}: hostile input ({what}) -> {} (treated as error, not accept; prefer exit 1)", o.describe())),
            }
        }
    }
    if honest.is_empty() {
        adv = LocalGate::skip(ObligationId::AdversarialProofs, "no honest proof to mutate");
    }
    gates.extend([conf, rel, adv, res]);
    drop(work);
    finish(gates, package_digest)
}

pub fn render_text(r: &LocalReport) -> String {
    let mut s = String::new();
    s.push_str(&format!("=== {} ===\n", r.banner));
    s.push_str(&format!("challenge: {}\n", r.challenge_id));
    if let Some(d) = &r.package_digest {
        s.push_str(&format!("package:   {d}\n"));
    }
    s.push_str(&format!("network isolated: {}\n\n", r.network_isolated));
    for g in &r.gates {
        let gate = serde_json::to_value(g.gate).unwrap();
        let st = serde_json::to_value(g.status).unwrap();
        let rcs: Vec<String> = g
            .reason_codes
            .iter()
            .map(|c| {
                serde_json::to_value(c)
                    .unwrap()
                    .as_str()
                    .unwrap()
                    .to_string()
            })
            .collect();
        s.push_str(&format!(
            "[{:<7}] {}{}\n",
            st.as_str().unwrap(),
            gate.as_str().unwrap(),
            if rcs.is_empty() {
                String::new()
            } else {
                format!("  ({})", rcs.join(", "))
            }
        ));
        for d in &g.details {
            for line in d.lines() {
                s.push_str(&format!("          {line}\n"));
            }
        }
    }
    s.push_str(&format!(
        "\nresult: {} (formal gates were NOT run; only the judge's verdict counts)\n=== {} ===\n",
        if r.ok {
            "local checks passed"
        } else {
            "local checks FAILED"
        },
        r.banner
    ));
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn lean_comment_stripping() {
        let s = "a /- sorry /- nested -/ axiom -/ b -- native_decide\nc";
        assert_eq!(strip_lean_comments(s), "a  b \nc");
    }
    #[test]
    fn hostile_variants_differ() {
        let p = b"proofbytes".to_vec();
        for (_, v) in hostile_variants(&p) {
            assert_ne!(v, p);
        }
    }
}
