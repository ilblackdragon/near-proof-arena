//! The seam through which the formal checker runs anything that touches
//! candidate content (elaboration, `.olean` loading, export, replay).
//!
//! `UntrustedRunner` mirrors the shape of the workspace `Sandbox` trait
//! (`runners/sandbox`, CONTRACTS.md §9): read-only mounts, one scratch dir,
//! fixed env, no network, wall timeout, outcome measured by the supervisor.
//! [`SandboxRunner`] adapts it to the shared runner sandbox
//! (`arena_sandbox::Sandbox`): `bwrap-dev` for development (refused unless
//! `ARENA_DEV_UNSAFE=1`, results tier-capped at `demo`), `firecracker` in
//! production.

use std::path::PathBuf;
use std::time::Duration;

#[derive(Clone, Debug)]
pub struct RunSpec {
    /// argv[0] must be an absolute path *inside* the sandbox.
    pub argv: Vec<String>,
    /// Complete environment (nothing is inherited).
    pub env: Vec<(String, String)>,
    /// (host, guest) read-only binds.
    pub ro: Vec<(PathBuf, PathBuf)>,
    /// (host, guest) read-write binds (scratch only).
    pub rw: Vec<(PathBuf, PathBuf)>,
    pub cwd: PathBuf,
    pub wall_timeout: Duration,
    /// Address-space cap (best effort in dev; Lean reserves large virtual ranges).
    pub mem_bytes: Option<u64>,
    /// Max bytes any single file written by the process may reach.
    pub max_file_bytes: u64,
    /// If set, stdout is streamed to this *host* file (for large exports)
    /// instead of being captured/truncated.
    pub stdout_file: Option<PathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunExit {
    Exited(i32),
    Signaled(i32),
    TimedOut,
}

#[derive(Clone, Debug)]
pub struct RunOutcome {
    pub exit: RunExit,
    pub wall: Duration,
    /// Truncated to `CAPTURE_LIMIT` bytes. Untrusted diagnostics only.
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

impl RunOutcome {
    pub fn success(&self) -> bool {
        self.exit == RunExit::Exited(0)
    }
}

/// Untrusted output capture limit (CONTRACTS.md §4: 64 KiB).
pub const CAPTURE_LIMIT: usize = 64 * 1024;
/// Larger limit for judge tools whose stdout is a structured report.
pub const REPORT_CAPTURE_LIMIT: usize = 64 * 1024 * 1024;

#[derive(Debug, thiserror::Error)]
pub enum InfraError {
    #[error("sandbox refused: {0}")]
    Refused(String),
    #[error("sandbox infrastructure: {0}")]
    Io(#[from] std::io::Error),
}

pub trait UntrustedRunner: Send + Sync {
    /// Identifier recorded in reports (e.g. `bwrap-dev`, `firecracker`).
    fn id(&self) -> &str;
    /// True if results produced through this runner must be tier-capped at `demo`.
    fn demo_only(&self) -> bool;
    fn run(&self, spec: &RunSpec, capture_limit: usize) -> Result<RunOutcome, InfraError>;
}

/// Adapter from the formal checker's seam to the shared runner sandbox
/// (`arena_sandbox::Sandbox`, CONTRACTS §9): `bwrap-dev` in development,
/// `firecracker` in production (once it supports read-write output dirs; the
/// checker needs them for `.olean` outputs and is refused otherwise).
pub struct SandboxRunner {
    sandbox: std::sync::Arc<dyn arena_sandbox::Sandbox>,
    /// Host dir for per-run stdout capture directories.
    work: PathBuf,
}

/// Guest dir used to capture a run's stdout into a host file.
const G_STDOUT: &str = "/arena/stdout";

impl SandboxRunner {
    pub fn new(sandbox: std::sync::Arc<dyn arena_sandbox::Sandbox>, work: impl Into<PathBuf>) -> Result<Self, InfraError> {
        let layout = sandbox.layout();
        if !layout.rw_binds {
            return Err(InfraError::Refused(format!(
                "sandbox backend {} does not support read-write output directories required by the formal checker",
                sandbox.name()
            )));
        }
        let work = work.into();
        std::fs::create_dir_all(&work)?;
        Ok(SandboxRunner { sandbox, work })
    }

    /// Development convenience: the shared `bwrap-dev` backend (refused
    /// unless `ARENA_DEV_UNSAFE=1`) with the sandbox helper at `helper`.
    pub fn bwrap_dev(helper: arena_sandbox::HelperCommand, work: impl Into<PathBuf>) -> Result<Self, InfraError> {
        let work = work.into();
        let sb = arena_sandbox::BwrapDev::new(arena_sandbox::BwrapConfig::new(helper, work.join("sandbox")))
            .map_err(|e| InfraError::Refused(e.to_string()))?;
        Self::new(std::sync::Arc::new(sb), work)
    }

    fn translate(&self, spec: &RunSpec, stdout_dir: Option<&std::path::Path>) -> arena_sandbox::SandboxSpec {
        let guest = |p: &PathBuf| p.display().to_string();
        let mut argv = spec.argv.clone();
        if stdout_dir.is_some() {
            let mut w = vec!["/bin/sh".to_string(), "-c".into(), format!("exec \"$0\" \"$@\" > {G_STDOUT}/out")];
            w.extend(argv);
            argv = w;
        }
        let mut s = arena_sandbox::SandboxSpec::new(argv);
        s.ro_mounts = spec.ro.iter().map(|(h, g)| arena_sandbox::Mount { host: h.clone(), guest: guest(g) }).collect();
        s.rw_binds = spec.rw.iter().map(|(h, g)| arena_sandbox::Mount { host: h.clone(), guest: guest(g) }).collect();
        if let Some(d) = stdout_dir {
            s.rw_binds.push(arena_sandbox::Mount { host: d.to_path_buf(), guest: G_STDOUT.into() });
        }
        s.env = spec.env.clone();
        s.cwd = guest(&spec.cwd);
        s.wall_timeout = spec.wall_timeout;
        // Lean reserves large virtual ranges: the memory cap is the cgroup's
        // (RSS-based) limit; 8 GiB when the checker sets none.
        s.mem_bytes = spec.mem_bytes.unwrap_or(8 << 30);
        s.pids = 1024;
        // RLIMIT_FSIZE inside the sandbox follows the scratch size.
        s.rw_scratch_mb = (spec.max_file_bytes >> 20).max(64);
        s.output_trunc_bytes = REPORT_CAPTURE_LIMIT;
        s
    }
}

impl UntrustedRunner for SandboxRunner {
    fn id(&self) -> &str {
        self.sandbox.name()
    }
    fn demo_only(&self) -> bool {
        self.sandbox.tier_cap() == Some(arena_types::challenge::Tier::Demo)
    }
    fn run(&self, spec: &RunSpec, capture_limit: usize) -> Result<RunOutcome, InfraError> {
        static N: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let stdout_dir = match &spec.stdout_file {
            Some(_) => {
                let d = self.work.join(format!(
                    "stdout-{}-{}",
                    std::process::id(),
                    N.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                ));
                std::fs::create_dir_all(&d)?;
                Some(d)
            }
            None => None,
        };
        let sspec = self.translate(spec, stdout_dir.as_deref());
        let res = self.sandbox.run(&sspec);
        let o = match res {
            Ok(o) => o,
            Err(arena_sandbox::InfraError::InvalidSpec(m)) | Err(arena_sandbox::InfraError::Refused(m)) => {
                return Err(InfraError::Refused(m))
            }
            Err(e) => return Err(InfraError::Io(std::io::Error::other(e.to_string()))),
        };
        if let (Some(d), Some(target)) = (&stdout_dir, &spec.stdout_file) {
            let src = d.join("out");
            // Regular file only: never follow anything the sandbox planted.
            let regular = std::fs::symlink_metadata(&src).map(|m| m.file_type().is_file()).unwrap_or(false);
            if regular {
                std::fs::rename(&src, target).or_else(|_| std::fs::copy(&src, target).map(|_| ()))?;
            } else {
                std::fs::File::create(target)?;
            }
            let _ = std::fs::remove_dir_all(d);
        }
        let exit = match o.exit {
            arena_sandbox::ExitStatus::Exited(c) => RunExit::Exited(c),
            arena_sandbox::ExitStatus::Signaled(s) => RunExit::Signaled(s),
            arena_sandbox::ExitStatus::TimedOut => RunExit::TimedOut,
            arena_sandbox::ExitStatus::OomKilled => RunExit::Signaled(libc::SIGKILL),
            arena_sandbox::ExitStatus::ExecFailed => RunExit::Exited(127),
        };
        let mut stdout = o.stdout_trunc;
        stdout.truncate(capture_limit);
        let mut stderr = o.stderr_trunc;
        stderr.truncate(CAPTURE_LIMIT);
        Ok(RunOutcome { exit, wall: Duration::from_nanos(o.wall_ns), stdout, stderr })
    }
}
