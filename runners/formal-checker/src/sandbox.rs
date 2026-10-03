//! The seam through which the formal checker runs anything that touches
//! candidate content (elaboration, `.olean` loading, export, replay).
//!
//! `UntrustedRunner` mirrors the shape of the workspace `Sandbox` trait
//! (`runners/sandbox`, CONTRACTS.md §9): read-only mounts, one scratch dir,
//! fixed env, no network, wall timeout, outcome measured by the supervisor.
//! Production plugs in the firecracker backend through an adapter; this crate
//! ships `BwrapDevRunner` (namespaces only, refused unless `ARENA_DEV_UNSAFE=1`,
//! results tier-capped at `demo`).

use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

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

/// bubblewrap namespace sandbox for development. `--unshare-all` (no network,
/// fresh pid/ipc/uts/user/cgroup namespaces), empty root with `/usr` read-only,
/// tmpfs `/tmp`, `--clearenv`, `--die-with-parent`, `--new-session`.
pub struct BwrapDevRunner {
    bwrap: PathBuf,
}

impl BwrapDevRunner {
    pub fn new() -> Result<Self, InfraError> {
        if std::env::var("ARENA_DEV_UNSAFE").as_deref() != Ok("1") {
            return Err(InfraError::Refused(
                "bwrap-dev runner requires ARENA_DEV_UNSAFE=1 (results are tier-capped at demo)".into(),
            ));
        }
        let bwrap = ["/usr/bin/bwrap", "/bin/bwrap"]
            .iter()
            .map(PathBuf::from)
            .find(|p| p.is_file())
            .ok_or_else(|| InfraError::Refused("bwrap not installed".into()))?;
        Ok(BwrapDevRunner { bwrap })
    }

    fn command(&self, spec: &RunSpec) -> Command {
        let mut c = Command::new(&self.bwrap);
        c.args(["--unshare-all", "--die-with-parent", "--new-session", "--clearenv"]);
        c.args(["--ro-bind", "/usr", "/usr"]);
        for (link, target) in [("/lib", "usr/lib"), ("/lib64", "usr/lib64"), ("/bin", "usr/bin")] {
            c.args(["--symlink", target, link]);
        }
        c.args(["--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp"]);
        for (h, g) in &spec.ro {
            c.arg("--ro-bind").arg(h).arg(g);
        }
        for (h, g) in &spec.rw {
            c.arg("--bind").arg(h).arg(g);
        }
        for (k, v) in &spec.env {
            c.args(["--setenv", k, v]);
        }
        c.arg("--chdir").arg(&spec.cwd);
        c.arg("--");
        c.args(&spec.argv);
        c
    }
}

fn set_limits(mem: Option<u64>, fsize: u64) -> std::io::Result<()> {
    unsafe {
        let lim = |res, v: u64| {
            let r = libc::rlimit { rlim_cur: v as libc::rlim_t, rlim_max: v as libc::rlim_t };
            if libc::setrlimit(res, &r) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        };
        lim(libc::RLIMIT_FSIZE, fsize)?;
        lim(libc::RLIMIT_CORE, 0)?;
        if let Some(m) = mem {
            lim(libc::RLIMIT_AS, m)?;
        }
    }
    Ok(())
}

fn read_capped<R: Read + Send + 'static>(mut r: R, cap: usize) -> std::thread::JoinHandle<Vec<u8>> {
    std::thread::spawn(move || {
        let mut out = Vec::new();
        let mut buf = [0u8; 8192];
        loop {
            match r.read(&mut buf) {
                Ok(0) | Err(_) => break,
                Ok(n) => {
                    let room = cap.saturating_sub(out.len());
                    out.extend_from_slice(&buf[..n.min(room)]);
                }
            }
        }
        out
    })
}

/// Spawn `cmd`, enforce the wall timeout, capture output. Shared by runners.
pub fn supervise(mut cmd: Command, spec: &RunSpec, capture_limit: usize) -> Result<RunOutcome, InfraError> {
    use std::os::unix::process::{CommandExt, ExitStatusExt};
    let mem = spec.mem_bytes;
    let fsize = spec.max_file_bytes;
    cmd.stdin(Stdio::null()).stderr(Stdio::piped());
    match &spec.stdout_file {
        Some(p) => {
            cmd.stdout(Stdio::from(std::fs::File::create(p)?));
        }
        None => {
            cmd.stdout(Stdio::piped());
        }
    }
    cmd.process_group(0);
    unsafe {
        cmd.pre_exec(move || set_limits(mem, fsize));
    }
    let start = Instant::now();
    let mut child = cmd.spawn()?;
    let out_t = child.stdout.take().map(|s| read_capped(s, capture_limit));
    let err_t = child.stderr.take().map(|s| read_capped(s, CAPTURE_LIMIT));
    let exit = loop {
        if let Some(st) = child.try_wait()? {
            break match (st.code(), st.signal()) {
                (Some(c), _) => RunExit::Exited(c),
                (None, Some(s)) => RunExit::Signaled(s),
                _ => RunExit::Signaled(0),
            };
        }
        if start.elapsed() > spec.wall_timeout {
            unsafe {
                libc::kill(-(child.id() as i32), libc::SIGKILL);
            }
            let _ = child.kill();
            let _ = child.wait();
            break RunExit::TimedOut;
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let wall = start.elapsed();
    let stdout = out_t.map(|t| t.join().unwrap_or_default()).unwrap_or_default();
    let stderr = err_t.map(|t| t.join().unwrap_or_default()).unwrap_or_default();
    Ok(RunOutcome { exit, wall, stdout, stderr })
}

impl UntrustedRunner for BwrapDevRunner {
    fn id(&self) -> &str {
        "bwrap-dev"
    }
    fn demo_only(&self) -> bool {
        true
    }
    fn run(&self, spec: &RunSpec, capture_limit: usize) -> Result<RunOutcome, InfraError> {
        supervise(self.command(spec), spec, capture_limit)
    }
}
