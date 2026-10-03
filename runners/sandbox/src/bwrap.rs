//! `bwrap-dev`: bubblewrap namespaces + (optionally) a transient delegated
//! cgroup v2 scope. **DEMO-only isolation**: refused unless
//! `ARENA_DEV_UNSAFE=1`, and every outcome is stamped
//! [`ISOLATION_LABEL`] with `tier_cap = Some(Demo)`.
//!
//! Process tree for one run:
//!
//! ```text
//! supervisor (this process)
//!  └─ systemd-run --user --scope -p Delegate=yes --unit arena-sbx-*   (optional)
//!      └─ arena-sandbox-helper shim       host side: cgroup, timeout, rusage
//!          └─ bwrap --unshare-all ...     (in <scope>/sandbox cgroup)
//!              └─ /.arena/helper init     PID 1 in the sandbox
//!                  └─ entry point         new session, rlimits
//! ```

use crate::helper::{self, InitConfig, InitExit, InitStatus, ShimConfig, ShimReport};
use crate::spec::*;
use arena_types::challenge::Tier;
use std::fs;
use std::io::{self, Read};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::OnceLock;
use std::time::Duration;

pub const BACKEND_NAME: &str = "bwrap-dev";
pub const ISOLATION_LABEL: &str = "bwrap-dev (DEMO-only)";
pub const DEV_UNSAFE_ENV: &str = "ARENA_DEV_UNSAFE";

/// Guest uid/gid of the sandboxed process.
const GUEST_ID: &str = "1000";
const SHM_BYTES: u64 = 16 << 20;
/// Extra wall time after `wall_timeout` before the supervisor stops waiting
/// for the shim and kills the whole helper tree itself.
const BACKSTOP: Duration = Duration::from_secs(30);

/// How to invoke the helper binary: `exe [prefix_args..] (shim|init) cfg`.
#[derive(Clone, Debug)]
pub struct HelperCommand {
    pub exe: PathBuf,
    pub prefix_args: Vec<String>,
}

impl HelperCommand {
    pub fn new(exe: impl Into<PathBuf>) -> Self {
        HelperCommand { exe: exe.into(), prefix_args: vec![] }
    }
    /// `$ARENA_SANDBOX_HELPER`, else `arena-sandbox-helper` next to the
    /// current executable.
    pub fn locate() -> io::Result<Self> {
        if let Some(p) = std::env::var_os("ARENA_SANDBOX_HELPER") {
            return Ok(Self::new(PathBuf::from(p)));
        }
        let exe = std::env::current_exe()?;
        let sib = exe.with_file_name("arena-sandbox-helper");
        if sib.is_file() {
            return Ok(Self::new(sib));
        }
        Err(io::Error::other("arena-sandbox-helper not found (set ARENA_SANDBOX_HELPER)"))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CgroupMode {
    /// Use systemd user delegation if a probe succeeds, else rlimits.
    Auto,
    /// Require a delegated cgroup; fail runs otherwise.
    Require,
    /// Never use cgroups (rlimit fallback only).
    Off,
}

#[derive(Clone, Debug)]
pub struct BwrapConfig {
    pub helper: HelperCommand,
    pub bwrap: PathBuf,
    /// Host directory for per-run temp files (configs). Created if missing.
    pub work_root: PathBuf,
    pub cgroup: CgroupMode,
}

impl BwrapConfig {
    pub fn new(helper: HelperCommand, work_root: impl Into<PathBuf>) -> Self {
        let cgroup = match std::env::var("ARENA_SANDBOX_CGROUP").as_deref() {
            Ok("off") => CgroupMode::Off,
            Ok("require") => CgroupMode::Require,
            _ => CgroupMode::Auto,
        };
        BwrapConfig { helper, bwrap: PathBuf::from("bwrap"), work_root: work_root.into(), cgroup }
    }
}

pub struct BwrapDev {
    cfg: BwrapConfig,
    use_cgroup: bool,
}

static RUN_COUNTER: AtomicU64 = AtomicU64::new(0);

fn probe_systemd_scope() -> bool {
    static PROBE: OnceLock<bool> = OnceLock::new();
    *PROBE.get_or_init(|| {
        let mut c = Command::new("systemd-run");
        c.args(["--user", "--scope", "--quiet", "--collect", "-p", "Delegate=yes", "--", "true"]);
        keep_systemd_env(&mut c);
        c.stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null());
        matches!(c.status(), Ok(s) if s.success())
    })
}

fn keep_systemd_env(c: &mut Command) {
    c.env_clear();
    for k in ["PATH", "XDG_RUNTIME_DIR", "DBUS_SESSION_BUS_ADDRESS"] {
        if let Some(v) = std::env::var_os(k) {
            c.env(k, v);
        }
    }
}

impl BwrapDev {
    /// Construct the backend. Refuses unless `ARENA_DEV_UNSAFE=1`.
    pub fn new(cfg: BwrapConfig) -> Result<Self, InfraError> {
        if std::env::var(DEV_UNSAFE_ENV).as_deref() != Ok("1") {
            return Err(InfraError::Refused(format!(
                "{BACKEND_NAME} provides DEMO-only isolation; set {DEV_UNSAFE_ENV}=1 to use it"
            )));
        }
        fs::create_dir_all(&cfg.work_root)?;
        let use_cgroup = match cfg.cgroup {
            CgroupMode::Off => false,
            CgroupMode::Auto => probe_systemd_scope(),
            CgroupMode::Require => {
                if !probe_systemd_scope() {
                    return Err(InfraError::Refused("delegated cgroup v2 (systemd --user) unavailable".into()));
                }
                true
            }
        };
        Ok(BwrapDev { cfg, use_cgroup })
    }

    pub fn uses_cgroup(&self) -> bool {
        self.use_cgroup
    }

    fn bwrap_args(&self, spec: &SandboxSpec, init_cfg: &Path) -> Result<Vec<String>, InfraError> {
        let mut a: Vec<String> = Vec::new();
        let mut push = |xs: &[&str]| a.extend(xs.iter().map(|s| s.to_string()));
        push(&[
            "--unshare-all",
            "--unshare-user",
            "--disable-userns",
            "--die-with-parent",
            "--new-session",
            "--as-pid-1",
            "--uid",
            GUEST_ID,
            "--gid",
            GUEST_ID,
            "--hostname",
            "arena-sandbox",
            "--clearenv",
        ]);
        let mut env: Vec<(String, String)> = vec![
            ("PATH".into(), "/usr/local/bin:/usr/bin:/bin".into()),
            ("HOME".into(), SCRATCH.into()),
            ("TMPDIR".into(), "/tmp".into()),
            ("LANG".into(), "C.UTF-8".into()),
            ("TZ".into(), "UTC".into()),
        ];
        for (k, v) in &spec.env {
            env.retain(|(ek, _)| ek != k);
            env.push((k.clone(), v.clone()));
        }
        for (k, v) in env {
            a.extend(["--setenv".into(), k, v]);
        }
        match &spec.rootfs {
            Rootfs::HostDev | Rootfs::BackendDefault => {
                a.extend(["--ro-bind".into(), "/usr".into(), "/usr".into()]);
                for top in ["bin", "sbin", "lib", "lib32", "lib64"] {
                    root_entry(&mut a, Path::new("/"), top)?;
                }
                for f in ["ld.so.cache", "ld.so.conf", "ld.so.conf.d", "alternatives"] {
                    a.extend(["--ro-bind-try".into(), format!("/etc/{f}"), format!("/etc/{f}")]);
                }
            }
            Rootfs::Image { path, .. } => {
                let mut names: Vec<String> = fs::read_dir(path)?
                    .filter_map(|e| e.ok()?.file_name().into_string().ok())
                    .filter(|n| !matches!(n.as_str(), "proc" | "dev" | "sys" | "tmp" | "run" | "scratch" | ".arena" | "in"))
                    .collect();
                names.sort();
                for n in names {
                    root_entry(&mut a, path, &n)?;
                }
            }
        }
        let mut push = |xs: &[&str]| a.extend(xs.iter().map(|s| s.to_string()));
        push(&["--proc", "/proc", "--dev", "/dev"]);
        let shm = SHM_BYTES.to_string();
        push(&["--size", &shm, "--tmpfs", "/dev/shm", "--remount-ro", "/dev"]);
        let scratch_bytes = (spec.rw_scratch_mb << 20).to_string();
        push(&["--size", &scratch_bytes, "--perms", "0755", "--tmpfs", SCRATCH]);
        push(&["--symlink", "/scratch/tmp", "/tmp"]);
        let helper = self.cfg.helper.exe.canonicalize()?;
        a.extend(["--ro-bind".into(), helper.display().to_string(), "/.arena/helper".into()]);
        a.extend(["--ro-bind".into(), init_cfg.display().to_string(), "/.arena/init.json".into()]);
        for m in &spec.ro_mounts {
            if !m.host.exists() {
                return Err(InfraError::InvalidSpec(format!("mount source {} missing", m.host.display())));
            }
            a.extend(["--ro-bind".into(), m.host.display().to_string(), m.guest.clone()]);
        }
        for m in &spec.rw_binds {
            if !m.host.is_dir() {
                return Err(InfraError::InvalidSpec(format!("rw bind source {} is not a directory", m.host.display())));
            }
            a.extend(["--bind".into(), m.host.display().to_string(), m.guest.clone()]);
        }
        let mut push = |xs: &[&str]| a.extend(xs.iter().map(|s| s.to_string()));
        push(&["--remount-ro", "/", "--chdir", "/", "/.arena/helper"]);
        a.extend(self.cfg.helper.prefix_args.iter().cloned());
        a.extend(["init".into(), "/.arena/init.json".into()]);
        Ok(a)
    }
}

/// Bind (or re-create as a symlink) one top-level rootfs entry.
fn root_entry(a: &mut Vec<String>, root: &Path, name: &str) -> Result<(), InfraError> {
    let p = root.join(name);
    let Ok(meta) = fs::symlink_metadata(&p) else { return Ok(()) };
    let guest = format!("/{name}");
    if meta.file_type().is_symlink() {
        let target = fs::read_link(&p)?;
        a.extend(["--symlink".into(), target.display().to_string(), guest]);
    } else {
        a.extend(["--ro-bind".into(), p.display().to_string(), guest]);
    }
    Ok(())
}

fn pipe() -> io::Result<(OwnedFd, OwnedFd)> {
    let mut fds = [0; 2];
    if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
        return Err(io::Error::last_os_error());
    }
    // Move both ends above 10 so dup2 onto 3..5 in the child never clobbers.
    let hi = |fd: RawFd| -> io::Result<OwnedFd> {
        let n = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 10) };
        unsafe { libc::close(fd) };
        if n < 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(unsafe { OwnedFd::from_raw_fd(n) })
    };
    Ok((hi(fds[0])?, hi(fds[1])?))
}

fn read_trunc<R: Read>(mut r: R, limit: usize) -> (Vec<u8>, u64) {
    let mut keep = Vec::new();
    let mut total = 0u64;
    let mut buf = [0u8; 16 * 1024];
    loop {
        match r.read(&mut buf) {
            Ok(0) | Err(_) => break,
            Ok(n) => {
                total += n as u64;
                let room = limit.saturating_sub(keep.len());
                keep.extend_from_slice(&buf[..n.min(room)]);
            }
        }
    }
    (keep, total)
}

fn read_json<T: serde::de::DeserializeOwned>(fd: OwnedFd, limit: u64) -> Option<T> {
    let mut s = Vec::new();
    let f = fs::File::from(fd);
    f.take(limit).read_to_end(&mut s).ok()?;
    serde_json::from_slice(&s).ok()
}

struct Collected {
    tree: Option<arena_archive::Tree>,
    error: Option<String>,
}

fn collect_thread(fd: OwnedFd, dest: Option<PathBuf>, max_bytes: u64) -> Collected {
    let mut f = fs::File::from(fd);
    let Some(dest) = dest else {
        let _ = io::copy(&mut f, &mut io::sink());
        return Collected { tree: None, error: None };
    };
    let limits = arena_archive::Limits {
        max_compressed_bytes: max_bytes.saturating_add(64 << 20),
        max_expanded_bytes: max_bytes,
        max_entries: 100_000,
        max_ratio: u64::MAX,
        ratio_slack_bytes: u64::MAX,
    };
    let r = arena_archive::ingest(&mut f, &dest, &limits);
    // Drain whatever is left so the init never blocks on a full pipe.
    let _ = io::copy(&mut f, &mut io::sink());
    match r {
        Ok(x) => Collected { tree: Some(x.tree), error: None },
        Err(e) => {
            let _ = fs::create_dir(&dest);
            Collected { tree: None, error: Some(e.to_string()) }
        }
    }
}

impl Sandbox for BwrapDev {
    fn name(&self) -> &str {
        BACKEND_NAME
    }
    fn tier_cap(&self) -> Option<Tier> {
        Some(Tier::Demo)
    }

    fn run(&self, spec: &SandboxSpec) -> Result<SandboxOutcome, InfraError> {
        if std::env::var(DEV_UNSAFE_ENV).as_deref() != Ok("1") {
            return Err(InfraError::Refused(format!("{DEV_UNSAFE_ENV}=1 not set")));
        }
        spec.validate()?;
        if let Some(d) = &spec.out_dir {
            if d.exists() {
                return Err(InfraError::InvalidSpec(format!("out_dir {} already exists", d.display())));
            }
        }
        let n = RUN_COUNTER.fetch_add(1, Ordering::Relaxed);
        let run_id = format!(
            "{}-{}-{}",
            std::process::id(),
            n,
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.subsec_nanos()).unwrap_or(0)
        );
        let run_dir = self.cfg.work_root.join(format!("run-{run_id}"));
        fs::create_dir(&run_dir)?;
        let _cleanup = RemoveOnDrop(run_dir.clone());

        let init_cfg = InitConfig {
            argv: spec.argv.clone(),
            cwd: spec.cwd.clone(),
            copy_in: spec.copy_in.clone(),
            mkdirs: spec.scratch_dirs.clone(),
            collect: spec.collect.clone(),
            scratch: SCRATCH.to_string(),
            fsize_bytes: spec.rw_scratch_mb << 20,
            fallback_rlimits: (!self.use_cgroup).then_some(helper::FallbackRlimits {
                as_bytes: spec.mem_bytes,
                nproc: spec.pids as u64,
            }),
        };
        let init_path = run_dir.join("init.json");
        fs::write(&init_path, serde_json::to_vec(&init_cfg).map_err(io::Error::other)?)?;
        let shim_cfg = ShimConfig {
            bwrap: which(&self.cfg.bwrap)?,
            bwrap_args: self.bwrap_args(spec, &init_path)?,
            use_cgroup: self.use_cgroup,
            mem_bytes: spec.mem_bytes,
            pids: spec.pids,
            cpu_set: spec.cpu_set.clone(),
            wall_timeout_ns: spec.wall_timeout.as_nanos() as u64,
        };
        let shim_path = run_dir.join("shim.json");
        fs::write(&shim_path, serde_json::to_vec(&shim_cfg).map_err(io::Error::other)?)?;

        let (tar_r, tar_w) = pipe()?;
        let (st_r, st_w) = pipe()?;
        let (shim_r, shim_w) = pipe()?;

        let mut cmd = if self.use_cgroup {
            let mut c = Command::new("systemd-run");
            c.args(["--user", "--scope", "--quiet", "--collect", "-p", "Delegate=yes"]);
            c.arg(format!("--unit={}{}", helper::SCOPE_PREFIX, run_id));
            c.arg("--");
            c.arg(&self.cfg.helper.exe);
            keep_systemd_env(&mut c);
            c
        } else {
            let mut c = Command::new(&self.cfg.helper.exe);
            c.env_clear();
            c
        };
        cmd.args(&self.cfg.helper.prefix_args).arg("shim").arg(&shim_path);
        cmd.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped()).process_group(0);
        let fds = [(tar_w.as_raw_fd(), helper::TAR_FD), (st_w.as_raw_fd(), helper::INIT_STATUS_FD), (shim_w.as_raw_fd(), helper::SHIM_STATUS_FD)];
        unsafe {
            cmd.pre_exec(move || {
                for (src, dst) in fds {
                    if libc::dup2(src, dst) < 0 {
                        return Err(io::Error::last_os_error());
                    }
                }
                Ok(())
            });
        }
        let mut child = cmd.spawn().map_err(|e| InfraError::Spawn(e.to_string()))?;
        drop((tar_w, st_w, shim_w));
        let pgid = child.id() as libc::pid_t;

        let trunc = spec.output_trunc_bytes;
        let so = child.stdout.take().expect("piped");
        let se = child.stderr.take().expect("piped");
        let t_out = std::thread::spawn(move || read_trunc(so, trunc));
        let t_err = std::thread::spawn(move || read_trunc(se, trunc));
        let dest = spec.out_dir.clone();
        let max_out = spec.max_output_bytes;
        let t_tar = std::thread::spawn(move || collect_thread(tar_r, dest, max_out));
        let t_st = std::thread::spawn(move || read_json::<InitStatus>(st_r, 1 << 20));
        let t_shim = std::thread::spawn(move || read_json::<ShimReport>(shim_r, 1 << 20));

        // Backstop: the shim enforces the timeout; we only intervene if the
        // shim itself wedges.
        let (tx, rx) = std::sync::mpsc::channel();
        let waiter = std::thread::spawn(move || {
            let r = child.wait();
            let _ = tx.send(());
            r
        });
        let mut backstop_fired = false;
        if rx.recv_timeout(spec.wall_timeout + BACKSTOP).is_err() {
            backstop_fired = true;
            unsafe {
                libc::killpg(pgid, libc::SIGKILL);
            }
        }
        let _ = waiter.join();
        let shim: Option<ShimReport> = t_shim.join().ok().flatten();
        let init: Option<InitStatus> = t_st.join().ok().flatten();
        let collected = t_tar.join().map_err(|_| InfraError::Supervisor("collector panicked".into()))?;
        let (stdout_trunc, stdout_bytes) = t_out.join().unwrap_or_default();
        let (stderr_trunc, stderr_bytes) = t_err.join().unwrap_or_default();

        let diag = || String::from_utf8_lossy(&stderr_trunc[..stderr_trunc.len().min(2048)]).into_owned();
        let Some(shim) = shim else {
            return Err(InfraError::Supervisor(format!(
                "no shim report (backstop fired: {backstop_fired}); stderr: {}",
                diag()
            )));
        };
        if let Some(e) = &shim.error {
            return Err(InfraError::Supervisor(format!("shim: {e}")));
        }
        let cg = shim.cgroup.as_ref();
        let oom = cg.map(|c| c.oom_kills > 0).unwrap_or(false);
        let exit = if shim.timed_out {
            ExitStatus::TimedOut
        } else if oom {
            ExitStatus::OomKilled
        } else {
            match &init {
                Some(st) if st.setup_error.is_some() => {
                    return Err(InfraError::Supervisor(format!("sandbox init setup: {}", st.setup_error.as_deref().unwrap_or(""))));
                }
                Some(st) if st.exec_error.is_some() => ExitStatus::ExecFailed,
                Some(InitStatus { exit: Some(InitExit::Code(c)), .. }) => ExitStatus::Exited(*c),
                Some(InitStatus { exit: Some(InitExit::Signal(s)), .. }) => ExitStatus::Signaled(*s),
                _ => {
                    return Err(InfraError::Supervisor(format!(
                        "sandbox init did not report (bwrap exit {:?}, signal {:?}); stderr: {}",
                        shim.bwrap_exit,
                        shim.bwrap_signal,
                        diag()
                    )))
                }
            }
        };
        let mut output_error = collected.error;
        if let Some(e) = init.as_ref().and_then(|s| s.collect_error.clone()) {
            output_error.get_or_insert(e);
        }
        let (outputs, outputs_tree) = match (&collected.tree, &output_error) {
            (Some(t), None) => (t.files.iter().map(|(p, f)| (p.clone(), f.digest.clone())).collect(), Some(t.digest())),
            _ => (vec![], None),
        };
        if output_error.is_some() {
            if let Some(d) = &spec.out_dir {
                let _ = fs::remove_dir_all(d);
                let _ = fs::create_dir(d);
            }
        }
        let complete = output_error.is_none();
        Ok(SandboxOutcome {
            exit,
            wall_ns: shim.wall_ns,
            cpu_ns: cg.map(|c| c.usage_ns).unwrap_or(shim.utime_ns + shim.stime_ns),
            peak_rss_bytes: cg.map(|c| c.peak_bytes).unwrap_or(shim.maxrss_bytes),
            max_process_rss_bytes: shim.maxrss_bytes,
            stdout_trunc,
            stderr_trunc,
            stdout_bytes,
            stderr_bytes,
            outputs,
            outputs_tree,
            output_error,
            pids_limit_hit: cg.map(|c| c.pids_max_events > 0).unwrap_or(false),
            limits: if cg.is_some() { LimitEnforcement::CgroupV2 } else { LimitEnforcement::Rlimit },
            isolation: ISOLATION_LABEL.to_string(),
            tier_cap: Some(Tier::Demo),
            entry_wall_ns: init.map(|s| s.entry_wall_ns),
            diagnostics: Diagnostics {
                backend: BACKEND_NAME.to_string(),
                total_ns: shim.wall_ns,
                outputs_complete: complete,
                ..Default::default()
            },
        })
    }
}

fn which(p: &Path) -> io::Result<PathBuf> {
    if p.components().count() > 1 {
        return Ok(p.to_path_buf());
    }
    let path = std::env::var_os("PATH").unwrap_or_else(|| "/usr/bin:/bin".into());
    for d in std::env::split_paths(&path) {
        let c = d.join(p);
        if c.is_file() {
            return Ok(c);
        }
    }
    Err(io::Error::other(format!("{} not found in PATH", p.display())))
}

struct RemoveOnDrop(PathBuf);
impl Drop for RemoveOnDrop {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
