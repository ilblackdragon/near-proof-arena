//! Job execution: the [`JobExecutor`] seam and the stage executor that runs
//! untrusted code only through [`arena_sandbox::Sandbox`].

use crate::jobs::*;
use crate::mutators::MutatorRegistry;
use crate::oracle::Oracles;
use crate::stages;
use crate::store::{ArtifactStore, StoreError};
use arena_sandbox::{InfraError, Mount, Rootfs, Sandbox, SandboxOutcome, SandboxSpec};
use arena_types::challenge::Tier;
use arena_types::{BenchmarkResult, CandidateManifest, Digest, EvidenceGraph, EvidenceRef, GateResult, ReasonCode};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

pub const WORKER_VERSION: &str = concat!("arena-worker/", env!("CARGO_PKG_VERSION"));

#[derive(Debug, thiserror::Error)]
pub enum ExecError {
    /// The sandbox reported a forged/malformed guest result: the candidate
    /// broke out of its process-level confinement. Becomes a FAIL with
    /// `SANDBOX_VIOLATION` on the job's primary gate.
    #[error("sandbox violation: {0}")]
    Violation(String),
    /// Judge-side failure: the job is failed as retryable.
    #[error("infra: {0}")]
    Infra(String),
    /// The job cannot be run by this worker at all (e.g. tier above the
    /// sandbox's cap): failed as non-retryable.
    #[error("refused: {0}")]
    Refused(String),
    /// Lease lost / cancelled mid-job.
    #[error("cancelled")]
    Cancelled,
}

impl From<InfraError> for ExecError {
    fn from(e: InfraError) -> Self {
        match e {
            InfraError::GuestProtocol(m) => ExecError::Violation(m),
            e => ExecError::Infra(format!("sandbox: {e}")),
        }
    }
}
impl From<StoreError> for ExecError {
    fn from(e: StoreError) -> Self {
        ExecError::Infra(format!("store: {e}"))
    }
}
impl From<std::io::Error> for ExecError {
    fn from(e: std::io::Error) -> Self {
        ExecError::Infra(format!("io: {e}"))
    }
}
impl From<arena_archive::ArchiveError> for ExecError {
    fn from(e: arena_archive::ArchiveError) -> Self {
        ExecError::Infra(format!("archive: {e}"))
    }
}

/// The seam between the worker daemon (lease/heartbeat/complete) and job
/// semantics.
pub trait JobExecutor: Send + Sync {
    /// `job_key` names the per-job work dir (job id + attempt).
    fn execute(&self, spec: &JobSpec, job_key: &str, cancel: &AtomicBool) -> Result<JobResult, ExecError>;
}

/// Toolchain available to build sandboxes when a job does not pin an image.
#[derive(Clone, Debug, Default)]
pub struct BuildEnv {
    /// Extra read-only mounts (e.g. a Rust toolchain at `/opt/rust`).
    pub mounts: Vec<Mount>,
    /// `PATH` inside the build sandbox.
    pub path: Option<String>,
    /// Extra allowlisted env (e.g. `CARGO_HOME`, `RUSTUP_HOME`).
    pub env: Vec<(String, String)>,
    /// Directory holding unpacked toolchain images: `<hex>/` (the tree,
    /// named by its TreeDigest) and `<hex>.json` (identity + `env`).
    pub images_dir: Option<PathBuf>,
    /// Pinned build toolchain image (TreeDigest) to build in. Required for
    /// production (non-demo) sandboxes; `None` = host-dev toolchain.
    pub toolchain_image: Option<Digest>,
}

/// Formal checker configuration (per challenge relation).
#[derive(Clone, Debug, Default, serde::Deserialize)]
pub struct FormalConfig {
    /// Keyed by `semantic_scope.formal_spec.relation_decl`.
    pub challenges: std::collections::HashMap<String, FormalChallengeConfig>,
}

#[derive(Clone, Debug, serde::Deserialize)]
pub struct FormalChallengeConfig {
    pub trusted: Vec<arena_formal_checker::TrustedPackage>,
    /// `TemplateExpected` JSON (module, decl, template, data).
    pub expected: serde_json::Value,
    #[serde(default)]
    pub conjunct_gates: Option<Vec<arena_types::ObligationId>>,
}

pub struct WorkerContext {
    pub worker_id: String,
    pub sandbox: Arc<dyn Sandbox>,
    pub store: Arc<dyn ArtifactStore>,
    pub work_root: PathBuf,
    pub build: BuildEnv,
    /// CPUs used for benchmark sandboxes.
    pub bench_cpus: Option<Vec<u32>>,
    /// DEV ONLY: cap on benchmark batch sizes (recorded in the result).
    pub bench_batch_cap: Option<u32>,
    /// Judge-sampled conformance cases (in addition to public fixtures).
    pub conformance_samples: usize,
    pub mutators: MutatorRegistry,
    pub oracles: Oracles,
    pub formal: Option<FormalConfig>,
    /// Keep per-job work dirs (debugging).
    pub keep_workdirs: bool,
}

/// Output of a stage before sandbox stamping.
#[derive(Default)]
pub struct StageOut {
    pub gates: Vec<GateResult>,
    pub manifest: Option<CandidateManifest>,
    pub build: Option<BuildOutputs>,
    pub benchmark: Option<BenchmarkResult>,
    pub evidence_graph: Option<EvidenceGraph>,
    pub log: Vec<String>,
    /// Whether candidate code ran in the sandbox (then gates are tier-capped
    /// by the backend).
    pub used_sandbox: bool,
}

/// Per-job scratch on the host, with helpers shared by the stages.
pub struct JobRun<'a> {
    pub ctx: &'a WorkerContext,
    pub dir: PathBuf,
    pub cancel: &'a AtomicBool,
    pub artifacts: Vec<NamedArtifact>,
    counter: u32,
}

pub const MAX_PACKAGE_BYTES: u64 = 256 << 20;
pub const MAX_BUNDLE_BYTES: u64 = 2 << 30;

impl<'a> JobRun<'a> {
    pub fn check_cancel(&self) -> Result<(), ExecError> {
        if self.cancel.load(Ordering::Relaxed) {
            return Err(ExecError::Cancelled);
        }
        Ok(())
    }

    /// A fresh, unused path under the job dir.
    pub fn fresh(&mut self, stem: &str) -> PathBuf {
        self.counter += 1;
        self.dir.join(format!("{stem}-{}", self.counter))
    }

    pub fn fetch(&self, d: &Digest, max: u64) -> Result<Vec<u8>, ExecError> {
        Ok(self.ctx.store.get(d, max)?)
    }

    pub fn write_file(&mut self, bytes: &[u8], stem: &str) -> Result<PathBuf, ExecError> {
        let p = self.fresh(stem);
        fs::write(&p, bytes)?;
        Ok(p)
    }

    /// Fetch a judge-produced tar artifact, ingest it safely and check that
    /// its TreeDigest is `want_tree`.
    pub fn fetch_tree(&mut self, archive: &Digest, want_tree: &Digest, max: u64, stem: &str) -> Result<arena_archive::Extracted, ExecError> {
        let b = self.fetch(archive, max.saturating_add(64 << 20))?;
        let dest = self.fresh(stem);
        let limits = arena_archive::Limits { max_expanded_bytes: max, max_compressed_bytes: max.saturating_add(64 << 20), ..Default::default() };
        let x = arena_archive::ingest_bytes(&b, &dest, &limits).map_err(|e| ExecError::Infra(format!("stored tree {archive}: {e}")))?;
        if &x.digest != want_tree {
            return Err(ExecError::Infra(format!("stored tree {archive} has TreeDigest {} but the run is bound to {want_tree}", x.digest)));
        }
        Ok(x)
    }

    /// Pack a host tree deterministically and upload it. Returns (archive
    /// digest, TreeDigest).
    pub fn upload_tree(&mut self, name: &str, root: &Path, tree: &arena_archive::Tree, public: bool) -> Result<(Digest, Digest), ExecError> {
        let tar = arena_archive::pack_tree(root, tree, Vec::new())?;
        let d = self.ctx.store.put(&tar)?;
        self.record(name, d.clone(), public, true);
        Ok((d, tree.digest()))
    }

    pub fn upload(&mut self, name: &str, bytes: &[u8], public: bool) -> Result<Digest, ExecError> {
        let d = self.ctx.store.put(bytes)?;
        self.record(name, d.clone(), public, true);
        Ok(d)
    }

    pub fn record(&mut self, name: &str, digest: Digest, public: bool, stored: bool) {
        self.artifacts.push(NamedArtifact { name: name.to_string(), digest, public, stored });
    }

    pub fn run(&self, spec: &SandboxSpec) -> Result<SandboxOutcome, ExecError> {
        self.check_cancel()?;
        Ok(self.ctx.sandbox.run(spec)?)
    }
}

/// Spec for running an entry point with read-only inputs, laid out per the
/// backend's [`GuestLayout`](arena_sandbox::GuestLayout): the bundle at
/// `<inputs>/bundle`, plus `files` (host path -> name under `<inputs>/`).
/// In `args`, a leading `@in/` expands to `<inputs>/` and `@scratch/` to
/// `<scratch>/`.
pub fn entry_spec(
    layout: &arena_sandbox::GuestLayout,
    bundle: &Path,
    entry: &str,
    args: &[&str],
    files: &[(&Path, &str)],
    timeout_ms: u64,
    limits: &RunLimits,
) -> SandboxSpec {
    let expand = |a: &str| {
        if let Some(rest) = a.strip_prefix("@in/") {
            format!("{}/{rest}", layout.inputs)
        } else if let Some(rest) = a.strip_prefix("@scratch/") {
            format!("{}/{rest}", layout.scratch)
        } else {
            a.to_string()
        }
    };
    let mut argv = vec![format!("{}/bundle/{entry}", layout.inputs)];
    argv.extend(args.iter().map(|a| expand(a)));
    let mut s = SandboxSpec::new(argv);
    s.rootfs = Rootfs::BackendDefault;
    s.cwd = layout.scratch.to_string();
    s.ro_mounts.push(Mount { host: bundle.to_path_buf(), guest: format!("{}/bundle", layout.inputs) });
    for (h, name) in files {
        s.ro_mounts.push(Mount { host: h.to_path_buf(), guest: format!("{}/{name}", layout.inputs) });
    }
    s.wall_timeout = std::time::Duration::from_millis(timeout_ms.max(1));
    s.mem_bytes = limits.max_ram_bytes.max(16 << 20);
    s.pids = limits.max_pids.max(4);
    s.rw_scratch_mb = limits.scratch_mb.max(8);
    s
}

/// Map a non-successful entry-point outcome to a reason code.
pub fn failure_reason(o: &SandboxOutcome) -> ReasonCode {
    match o.exit {
        arena_sandbox::ExitStatus::TimedOut => ReasonCode::Timeout,
        arena_sandbox::ExitStatus::OomKilled => ReasonCode::ResourceLimit,
        _ if o.pids_limit_hit => ReasonCode::ResourceLimit,
        _ => ReasonCode::ProverFailed,
    }
}

pub fn describe_exit(o: &SandboxOutcome) -> String {
    let mut s = match o.exit {
        arena_sandbox::ExitStatus::Exited(c) => format!("exit {c}"),
        arena_sandbox::ExitStatus::Signaled(s) => format!("signal {s}"),
        arena_sandbox::ExitStatus::TimedOut => "timed out".into(),
        arena_sandbox::ExitStatus::OomKilled => "OOM-killed".into(),
        arena_sandbox::ExitStatus::ExecFailed => "could not execute".into(),
    };
    if o.pids_limit_hit {
        s.push_str(" (process limit hit)");
    }
    s
}

fn tier_rank(t: Tier) -> u8 {
    match t {
        Tier::Demo => 0,
        Tier::Experimental => 1,
        Tier::Formal => 2,
    }
}

pub struct StageExecutor {
    pub ctx: WorkerContext,
}

impl StageExecutor {
    pub fn new(ctx: WorkerContext) -> Self {
        StageExecutor { ctx }
    }

    /// Highest tier this worker's sandbox can produce.
    pub fn tier_cap(&self) -> Tier {
        self.ctx.sandbox.tier_cap().unwrap_or(Tier::Formal)
    }

    pub fn execution_info(&self) -> ExecutionInfo {
        ExecutionInfo { sandbox_backend: self.ctx.sandbox.name().to_string(), tier_cap: self.tier_cap(), worker_version: WORKER_VERSION.to_string() }
    }

    /// Job kinds this worker can run.
    pub fn kinds(&self) -> Vec<JobKind> {
        JobKind::ALL
            .into_iter()
            .filter(|k| *k != JobKind::FormalCheck || (self.ctx.formal.is_some() && self.ctx.sandbox.layout().rw_binds))
            .collect()
    }

    fn isolation_label(&self) -> String {
        if self.ctx.sandbox.tier_cap() == Some(Tier::Demo) {
            arena_sandbox::ISOLATION_LABEL.to_string()
        } else {
            self.ctx.sandbox.name().to_string()
        }
    }
}

impl JobExecutor for StageExecutor {
    fn execute(&self, spec: &JobSpec, job_key: &str, cancel: &AtomicBool) -> Result<JobResult, ExecError> {
        let ctx = spec.ctx();
        if tier_rank(ctx.tier) > tier_rank(self.tier_cap()) {
            return Err(ExecError::Refused(format!("job tier {:?} exceeds this worker's sandbox cap {:?}", ctx.tier, self.tier_cap())));
        }
        fs::create_dir_all(&self.ctx.work_root)?;
        let dir = self.ctx.work_root.join(format!("job-{}", sanitize_id(job_key)));
        if dir.exists() {
            fs::remove_dir_all(&dir)?;
        }
        fs::create_dir(&dir)?;
        let mut run = JobRun { ctx: &self.ctx, dir: dir.clone(), cancel, artifacts: vec![], counter: 0 };
        let res = match spec {
            JobSpec::Validate(j) => stages::validate::run(&mut run, j),
            JobSpec::Build(j) => stages::build::run(&mut run, j),
            JobSpec::FormalCheck(j) => stages::formal::run(&mut run, j),
            JobSpec::Conformance(j) => stages::conformance::run(&mut run, j),
            JobSpec::Adversarial(j) => stages::adversarial::run(&mut run, j),
            JobSpec::Benchmark(j) => stages::benchmark::run(&mut run, j),
        };
        let artifacts = std::mem::take(&mut run.artifacts);
        if !self.ctx.keep_workdirs {
            let _ = fs::remove_dir_all(&dir);
        }
        let kind = spec.kind();
        let mut out = match res {
            Err(ExecError::Violation(m)) => {
                let mut g = crate::gate::Gate::start(primary_gate(kind));
                g.fail(ReasonCode::SandboxViolation, format!("sandbox reported a forged or malformed guest result: {m}"));
                StageOut { gates: vec![g.finish(arena_types::GateStatus::Unknown, true)], used_sandbox: true, ..Default::default() }
            }
            r => r?,
        };
        // Only owned gates may be reported (the server rejects others).
        let owned = kind.owned_gates();
        if let Some(g) = out.gates.iter().find(|g| !owned.contains(&g.gate)) {
            return Err(ExecError::Infra(format!("internal: {kind} stage produced foreign gate {:?}", g.gate)));
        }
        let label = self.isolation_label();
        if out.used_sandbox && self.ctx.sandbox.tier_cap() == Some(Tier::Demo) {
            for g in &mut out.gates {
                if !g.reason_codes.contains(&ReasonCode::DemoOnly) {
                    g.reason_codes.push(ReasonCode::DemoOnly);
                }
                g.summary = crate::gate::sanitize(&format!("[{label}] {}", g.summary));
            }
            if let Some(b) = &mut out.benchmark {
                b.measured_by = format!("{} via {label}", b.measured_by);
            }
        }
        let log = out.log.join("\n");
        let log_excerpt = (!log.is_empty()).then(|| crate::gate::sanitize(&log));
        Ok(JobResult {
            gates: out.gates,
            artifacts: artifacts
                .into_iter()
                .filter(|a| a.stored)
                .map(|a| EvidenceRef { label: a.name, digest: a.digest, public: a.public })
                .collect(),
            benchmark: out.benchmark,
            evidence_graph: out.evidence_graph,
            manifest: out.manifest,
            build: out.build,
            execution: self.execution_info(),
            log_excerpt,
        })
    }
}

/// The gate a job kind is primarily responsible for.
pub fn primary_gate(k: JobKind) -> arena_types::ObligationId {
    use arena_types::ObligationId::*;
    match k {
        JobKind::Validate => PkgWellformed,
        JobKind::Build => BuildReproducible,
        JobKind::FormalCheck => AxiomAudit,
        JobKind::Conformance => ConformanceDifferential,
        JobKind::Adversarial => AdversarialProofs,
        JobKind::Benchmark => Benchmark,
    }
}

fn sanitize_id(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() || c == '-' || c == '_' { c } else { '_' }).take(80).collect()
}

/// Seed parts binding sampled workloads to this challenge + package.
pub fn seed_parts(ctx: &JobContext) -> [String; 2] {
    [ctx.challenge_id.clone(), ctx.package_digest.to_string()]
}
