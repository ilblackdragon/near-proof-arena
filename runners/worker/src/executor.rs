//! Job execution: the [`JobExecutor`] seam and the stage executor that runs
//! untrusted code only through [`arena_sandbox::Sandbox`].

use crate::jobs::*;
use crate::mutators::MutatorRegistry;
use crate::store::{ArtifactStore, StoreError};
use crate::stages;
use arena_sandbox::{InfraError, Mount, Rootfs, Sandbox, SandboxOutcome, SandboxSpec};
use arena_types::challenge::Tier;
use arena_types::{Digest, ReasonCode};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[derive(Debug, thiserror::Error)]
pub enum ExecError {
    /// Judge-side failure: the job is failed as retryable.
    #[error("infra: {0}")]
    Infra(String),
    /// Lease lost / cancelled mid-job.
    #[error("cancelled")]
    Cancelled,
}

impl From<InfraError> for ExecError {
    fn from(e: InfraError) -> Self {
        ExecError::Infra(format!("sandbox: {e}"))
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
/// semantics. The server lane's job types plug in by converting to
/// [`Job`].
pub trait JobExecutor: Send + Sync {
    fn execute(&self, job: &Job, cancel: &AtomicBool) -> Result<JobOutput, ExecError>;
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
    /// Directory holding unpacked toolchain images, one per `<hex digest>`.
    pub images_dir: Option<PathBuf>,
}

pub struct WorkerContext {
    pub worker_id: String,
    pub sandbox: Arc<dyn Sandbox>,
    pub store: Arc<dyn ArtifactStore>,
    pub work_root: PathBuf,
    pub build: BuildEnv,
    /// CPUs used for benchmark sandboxes.
    pub bench_cpus: Option<Vec<u32>>,
    pub mutators: MutatorRegistry,
    /// Keep per-job work dirs (debugging).
    pub keep_workdirs: bool,
}

/// Output of a stage before sandbox stamping.
#[derive(Default)]
pub struct StageOut {
    pub gates: Vec<arena_types::GateResult>,
    pub artifacts: Vec<NamedArtifact>,
    pub manifest: Option<arena_types::CandidateManifest>,
    pub benchmark: Option<arena_types::BenchmarkResult>,
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

    pub fn fetch_file(&mut self, d: &Digest, max: u64, stem: &str) -> Result<PathBuf, ExecError> {
        let b = self.fetch(d, max)?;
        let p = self.fresh(stem);
        fs::write(&p, b)?;
        Ok(p)
    }

    /// Fetch a judge-produced tar artifact and ingest it safely.
    pub fn fetch_tree(&mut self, d: &Digest, max: u64, stem: &str) -> Result<arena_archive::Extracted, ExecError> {
        let b = self.fetch(d, max.saturating_add(64 << 20))?;
        let dest = self.fresh(stem);
        let limits = arena_archive::Limits { max_expanded_bytes: max, max_compressed_bytes: max.saturating_add(64 << 20), ..Default::default() };
        arena_archive::ingest_bytes(&b, &dest, &limits).map_err(|e| ExecError::Infra(format!("stored tree {d}: {e}")))
    }

    /// Pack a host tree deterministically, upload it, record both the tar
    /// digest (`name`) and the TreeDigest (`name_tree`).
    pub fn upload_tree(&mut self, name: &str, root: &Path, tree: &arena_archive::Tree, public: bool) -> Result<(Digest, Digest), ExecError> {
        let tar = arena_archive::pack_tree(root, tree, Vec::new())?;
        let d = self.ctx.store.put(&tar)?;
        let td = tree.digest();
        self.record(name, d.clone(), public, true);
        self.record(&format!("{name}_tree"), td.clone(), public, false);
        Ok((d, td))
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

/// Spec for running an entry point with read-only inputs: the bundle at
/// `/in/bundle`, plus `files` (host path -> guest path under `/in/`).
pub fn entry_spec(bundle: &Path, entry: &str, args: Vec<String>, files: &[(&Path, &str)], timeout_ms: u64, limits: &RunLimits) -> SandboxSpec {
    let mut argv = vec![format!("/in/bundle/{entry}")];
    argv.extend(args);
    let mut s = SandboxSpec::new(argv);
    s.rootfs = Rootfs::HostDev;
    s.ro_mounts.push(Mount { host: bundle.to_path_buf(), guest: "/in/bundle".into() });
    for (h, g) in files {
        s.ro_mounts.push(Mount { host: h.to_path_buf(), guest: (*g).to_string() });
    }
    s.wall_timeout = std::time::Duration::from_millis(timeout_ms.max(1));
    s.mem_bytes = limits.max_ram_bytes.max(16 << 20);
    s.pids = limits.max_pids.max(4);
    s.rw_scratch_mb = limits.scratch_mb.max(1);
    s
}

/// Map a non-successful entry-point outcome to a reason code.
pub fn failure_reason(o: &SandboxOutcome) -> ReasonCode {
    match o.exit {
        arena_sandbox::ExitStatus::TimedOut => ReasonCode::Timeout,
        arena_sandbox::ExitStatus::OomKilled => ReasonCode::ResourceLimit,
        _ => ReasonCode::ProverFailed,
    }
}

pub fn describe_exit(o: &SandboxOutcome) -> String {
    match o.exit {
        arena_sandbox::ExitStatus::Exited(c) => format!("exit {c}"),
        arena_sandbox::ExitStatus::Signaled(s) => format!("signal {s}"),
        arena_sandbox::ExitStatus::TimedOut => "timed out".into(),
        arena_sandbox::ExitStatus::OomKilled => "OOM-killed".into(),
        arena_sandbox::ExitStatus::ExecFailed => "could not execute".into(),
    }
}

pub struct StageExecutor {
    pub ctx: WorkerContext,
}

impl StageExecutor {
    pub fn new(ctx: WorkerContext) -> Self {
        StageExecutor { ctx }
    }

    pub fn sandbox_info(&self) -> SandboxInfo {
        SandboxInfo {
            backend: self.ctx.sandbox.name().to_string(),
            isolation: if self.ctx.sandbox.tier_cap() == Some(Tier::Demo) {
                arena_sandbox::ISOLATION_LABEL.to_string()
            } else {
                self.ctx.sandbox.name().to_string()
            },
            tier_cap: self.ctx.sandbox.tier_cap(),
        }
    }
}

impl JobExecutor for StageExecutor {
    fn execute(&self, job: &Job, cancel: &AtomicBool) -> Result<JobOutput, ExecError> {
        fs::create_dir_all(&self.ctx.work_root)?;
        let dir = self.ctx.work_root.join(format!("job-{}-{}", sanitize_id(&job.id), job.attempt));
        if dir.exists() {
            fs::remove_dir_all(&dir)?;
        }
        fs::create_dir(&dir)?;
        let mut run = JobRun { ctx: &self.ctx, dir: dir.clone(), cancel, artifacts: vec![], counter: 0 };
        let res = match &job.spec {
            JobSpec::Validate(j) => stages::validate::run(&mut run, j),
            JobSpec::Build(j) => stages::build::run(&mut run, j),
            JobSpec::Conformance(j) => stages::conformance::run(&mut run, j),
            JobSpec::Adversarial(j) => stages::adversarial::run(&mut run, j),
            JobSpec::Benchmark(j) => stages::benchmark::run(&mut run, j),
        };
        let artifacts = std::mem::take(&mut run.artifacts);
        if !self.ctx.keep_workdirs {
            let _ = fs::remove_dir_all(&dir);
        }
        let mut out = res?;
        let info = self.sandbox_info();
        if out.used_sandbox && info.tier_cap == Some(Tier::Demo) {
            for g in &mut out.gates {
                if !g.reason_codes.contains(&ReasonCode::DemoOnly) {
                    g.reason_codes.push(ReasonCode::DemoOnly);
                }
                g.summary = crate::gate::sanitize(&format!("[{}] {}", info.isolation, g.summary));
            }
            if let Some(b) = &mut out.benchmark {
                b.measured_by = format!("{} via {}", b.measured_by, info.isolation);
            }
        }
        let mut all = artifacts;
        all.extend(out.artifacts);
        Ok(JobOutput {
            job_id: job.id.clone(),
            gates: out.gates,
            artifacts: all,
            manifest: out.manifest,
            benchmark: out.benchmark,
            sandbox: info,
            worker_id: self.ctx.worker_id.clone(),
        })
    }
}

fn sanitize_id(s: &str) -> String {
    s.chars().map(|c| if c.is_ascii_alphanumeric() || c == '-' || c == '_' { c } else { '_' }).take(64).collect()
}
