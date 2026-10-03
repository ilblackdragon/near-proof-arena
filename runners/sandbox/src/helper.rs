//! The judge-side helper processes used by the `bwrap-dev` backend.
//!
//! One binary, two roles (`arena-sandbox-helper shim|init <config.json>`):
//!
//! * **shim** runs on the host, *outside* the sandbox (optionally inside a
//!   transient delegated systemd scope). It creates a child cgroup with the
//!   memory/pids/cpu limits, starts `bwrap` inside it, enforces the wall
//!   timeout, and measures wall time, rusage and cgroup statistics. It
//!   reports a [`ShimReport`] on fd [`SHIM_STATUS_FD`].
//! * **init** runs *inside* the sandbox as PID 1 of its PID namespace
//!   (non-dumpable, so the candidate, which runs as the same uid, cannot
//!   ptrace it or read its memory, and as PID 1 it ignores signals from inside
//!   the namespace). It copies inputs into scratch, starts the entry point in
//!   a new session, reaps everything, kills every leftover process once the
//!   entry point exits, then streams the requested outputs as a tar on fd
//!   [`TAR_FD`] and an [`InitStatus`] on fd [`INIT_STATUS_FD`].
//!
//! Neither role trusts anything the candidate wrote: the host side re-ingests
//! the tar with `arena-archive`'s hostile-archive checks.

use crate::spec::CopyIn;
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::{self, Read, Write};
use std::os::fd::{FromRawFd, RawFd};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

pub const TAR_FD: RawFd = 3;
pub const INIT_STATUS_FD: RawFd = 4;
pub const SHIM_STATUS_FD: RawFd = 5;

/// Cgroup scopes created for sandboxes carry this unit-name prefix; the shim
/// refuses to manage any other cgroup.
pub const SCOPE_PREFIX: &str = "arena-sbx-";

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FallbackRlimits {
    pub as_bytes: u64,
    pub nproc: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InitConfig {
    pub argv: Vec<String>,
    pub cwd: String,
    pub copy_in: Vec<CopyIn>,
    pub mkdirs: Vec<String>,
    pub collect: Vec<String>,
    pub scratch: String,
    pub fsize_bytes: u64,
    pub fallback_rlimits: Option<FallbackRlimits>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InitExit {
    Code(i32),
    Signal(i32),
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct InitStatus {
    pub exit: Option<InitExit>,
    pub exec_error: Option<String>,
    pub setup_error: Option<String>,
    pub collect_error: Option<String>,
    pub entry_wall_ns: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShimConfig {
    pub bwrap: PathBuf,
    pub bwrap_args: Vec<String>,
    pub use_cgroup: bool,
    pub mem_bytes: u64,
    pub pids: u32,
    pub cpu_set: Option<Vec<u32>>,
    pub wall_timeout_ns: u64,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct CgroupStats {
    pub path: String,
    pub peak_bytes: u64,
    pub usage_ns: u64,
    pub oom_kills: u64,
    pub pids_max_events: u64,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ShimReport {
    pub wall_ns: u64,
    pub timed_out: bool,
    pub bwrap_exit: Option<i32>,
    pub bwrap_signal: Option<i32>,
    pub utime_ns: u64,
    pub stime_ns: u64,
    pub maxrss_bytes: u64,
    pub cgroup: Option<CgroupStats>,
    pub error: Option<String>,
}

/// Entry point for the helper binary. `args` excludes argv[0] and any
/// dispatch prefix.
pub fn helper_main(args: &[String]) -> i32 {
    match args {
        [role, cfg] if role == "init" => init_main(Path::new(cfg)),
        [role, cfg] if role == "shim" => shim_main(Path::new(cfg)),
        _ => {
            eprintln!("usage: arena-sandbox-helper (init|shim) <config.json>");
            2
        }
    }
}

fn set_cloexec(fd: RawFd) {
    unsafe {
        let fl = libc::fcntl(fd, libc::F_GETFD);
        if fl >= 0 {
            libc::fcntl(fd, libc::F_SETFD, fl | libc::FD_CLOEXEC);
        }
    }
}

fn write_json_fd<T: Serialize>(fd: RawFd, v: &T) {
    // Takes ownership of the fd; closing it signals EOF to the reader.
    let mut f = unsafe { fs::File::from_raw_fd(fd) };
    let _ = serde_json::to_writer(&mut f, v);
    let _ = f.flush();
}

// --------------------------------------------------------------------------
// init (inside the sandbox)
// --------------------------------------------------------------------------

fn init_main(cfg_path: &Path) -> i32 {
    unsafe {
        libc::prctl(libc::PR_SET_DUMPABLE, 0, 0, 0, 0);
    }
    set_cloexec(TAR_FD);
    set_cloexec(INIT_STATUS_FD);
    let mut st = InitStatus::default();
    let cfg: InitConfig = match fs::read(cfg_path).map_err(|e| e.to_string()).and_then(|b| serde_json::from_slice(&b).map_err(|e| e.to_string())) {
        Ok(c) => c,
        Err(e) => {
            st.setup_error = Some(format!("init config: {e}"));
            write_json_fd(INIT_STATUS_FD, &st);
            return 0;
        }
    };
    let scratch = PathBuf::from(&cfg.scratch);
    if let Err(e) = init_setup(&cfg, &scratch) {
        st.setup_error = Some(e.to_string());
        drop(unsafe { fs::File::from_raw_fd(TAR_FD) });
        write_json_fd(INIT_STATUS_FD, &st);
        return 0;
    }

    let mut cmd = Command::new(&cfg.argv[0]);
    cmd.args(&cfg.argv[1..]).current_dir(&cfg.cwd).env("PWD", &cfg.cwd).stdin(Stdio::null());
    let fsize = cfg.fsize_bytes;
    let fb = cfg.fallback_rlimits.clone();
    unsafe {
        cmd.pre_exec(move || {
            if libc::setsid() < 0 {
                return Err(io::Error::last_os_error());
            }
            setrlimit(libc::RLIMIT_CORE, 0)?;
            setrlimit(libc::RLIMIT_FSIZE, fsize)?;
            setrlimit(libc::RLIMIT_NOFILE, 4096)?;
            if let Some(fb) = &fb {
                setrlimit(libc::RLIMIT_AS, fb.as_bytes)?;
                setrlimit(libc::RLIMIT_NPROC, fb.nproc)?;
            }
            Ok(())
        });
    }
    let start = Instant::now();
    match cmd.spawn() {
        Err(e) => st.exec_error = Some(e.to_string()),
        Ok(child) => {
            let pid = child.id() as libc::pid_t;
            loop {
                let mut status = 0;
                let r = unsafe { libc::waitpid(-1, &mut status, 0) };
                if r == pid {
                    st.entry_wall_ns = start.elapsed().as_nanos() as u64;
                    st.exit = Some(if libc::WIFEXITED(status) {
                        InitExit::Code(libc::WEXITSTATUS(status))
                    } else {
                        InitExit::Signal(libc::WTERMSIG(status))
                    });
                    break;
                }
                if r < 0 && io::Error::last_os_error().raw_os_error() != Some(libc::EINTR) {
                    break;
                }
            }
        }
    }
    // Nothing the entry point started may outlive it.
    unsafe {
        libc::kill(-1, libc::SIGKILL);
    }
    loop {
        let r = unsafe { libc::waitpid(-1, std::ptr::null_mut(), 0) };
        if r < 0 && io::Error::last_os_error().raw_os_error() != Some(libc::EINTR) {
            break;
        }
    }

    let tar_out = unsafe { fs::File::from_raw_fd(TAR_FD) };
    if let Err(e) = collect_outputs(&scratch, &cfg.collect, io::BufWriter::with_capacity(1 << 16, tar_out), &mut st) {
        st.collect_error.get_or_insert(e.to_string());
    }
    write_json_fd(INIT_STATUS_FD, &st);
    0
}

fn setrlimit(res: libc::__rlimit_resource_t, v: u64) -> io::Result<()> {
    let lim = libc::rlimit { rlim_cur: v as libc::rlim_t, rlim_max: v as libc::rlim_t };
    if unsafe { libc::setrlimit(res, &lim) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

fn init_setup(cfg: &InitConfig, scratch: &Path) -> io::Result<()> {
    if cfg.argv.is_empty() {
        return Err(io::Error::other("empty argv"));
    }
    let tmp = scratch.join("tmp");
    fs::DirBuilder::new().mode(0o700).create(&tmp)?;
    for c in &cfg.copy_in {
        let dst = scratch.join(&c.to_scratch);
        if let Some(parent) = dst.parent() {
            fs::create_dir_all(parent)?;
        }
        copy_tree(Path::new(&c.from_guest), &dst)?;
    }
    for d in &cfg.mkdirs {
        fs::create_dir_all(scratch.join(d))?;
    }
    Ok(())
}

fn copy_tree(src: &Path, dst: &Path) -> io::Result<()> {
    let meta = fs::symlink_metadata(src)?;
    let ft = meta.file_type();
    if ft.is_dir() {
        fs::DirBuilder::new().mode(0o755).create(dst)?;
        let mut names: Vec<_> = fs::read_dir(src)?.map(|e| e.map(|e| e.file_name())).collect::<Result<_, _>>()?;
        names.sort();
        for n in names {
            copy_tree(&src.join(&n), &dst.join(&n))?;
        }
        Ok(())
    } else if ft.is_file() {
        let mut from = fs::OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(src)?;
        let perms = if meta.permissions().mode() & 0o111 != 0 { 0o755 } else { 0o644 };
        let mut to = fs::OpenOptions::new().write(true).create_new(true).mode(perms).custom_flags(libc::O_NOFOLLOW).open(dst)?;
        io::copy(&mut from, &mut to)?;
        Ok(())
    } else {
        Err(io::Error::other(format!("refusing to copy non-regular file {}", src.display())))
    }
}

fn collect_outputs<W: Write>(scratch: &Path, collect: &[String], out: W, st: &mut InitStatus) -> io::Result<()> {
    let mut b = tar::Builder::new(out);
    for rel in collect {
        add_path(&mut b, scratch, rel, st)?;
    }
    b.into_inner()?.flush()
}

fn add_path<W: Write>(b: &mut tar::Builder<W>, scratch: &Path, rel: &str, st: &mut InitStatus) -> io::Result<()> {
    let p = scratch.join(rel);
    let meta = match fs::symlink_metadata(&p) {
        Ok(m) => m,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(e) => return Err(e),
    };
    let ft = meta.file_type();
    let mut h = tar::Header::new_gnu();
    h.set_mtime(0);
    h.set_uid(0);
    h.set_gid(0);
    if ft.is_dir() {
        h.set_entry_type(tar::EntryType::Directory);
        h.set_mode(0o755);
        h.set_size(0);
        b.append_data(&mut h, format!("{rel}/"), io::empty())?;
        let mut names = Vec::new();
        for e in fs::read_dir(&p)? {
            match e?.file_name().into_string() {
                Ok(n) => names.push(n),
                Err(n) => {
                    st.collect_error.get_or_insert(format!("non-UTF-8 output name {n:?} in {rel}"));
                }
            }
        }
        names.sort();
        for n in names {
            add_path(b, scratch, &format!("{rel}/{n}"), st)?;
        }
    } else if ft.is_file() {
        let f = fs::OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(&p)?;
        let len = f.metadata()?.len();
        h.set_entry_type(tar::EntryType::Regular);
        h.set_mode(if meta.permissions().mode() & 0o111 != 0 { 0o755 } else { 0o644 });
        h.set_size(len);
        b.append_data(&mut h, rel, f.take(len))?;
    } else {
        st.collect_error.get_or_insert(format!("output {rel:?} is not a regular file or directory"));
    }
    Ok(())
}

// --------------------------------------------------------------------------
// shim (host side)
// --------------------------------------------------------------------------

struct Cgroup {
    sandbox: PathBuf,
}

fn cg_write(p: &Path, v: &str) -> io::Result<()> {
    fs::write(p, v).map_err(|e| io::Error::new(e.kind(), format!("{}: {e}", p.display())))
}

fn cg_read(p: &Path) -> io::Result<String> {
    fs::read_to_string(p)
}

fn cg_kv(text: &str, key: &str) -> Option<u64> {
    text.lines().find_map(|l| {
        let mut it = l.split_whitespace();
        (it.next() == Some(key)).then(|| it.next()?.parse().ok()).flatten()
    })
}

fn setup_cgroup(cfg: &ShimConfig) -> io::Result<Cgroup> {
    let text = fs::read_to_string("/proc/self/cgroup")?;
    let rel = text
        .lines()
        .find_map(|l| l.strip_prefix("0::"))
        .ok_or_else(|| io::Error::other("no cgroup v2 membership"))?
        .trim()
        .trim_start_matches('/');
    let leaf = rel.rsplit('/').next().unwrap_or("");
    if !(leaf.starts_with(SCOPE_PREFIX) && leaf.ends_with(".scope")) {
        return Err(io::Error::other(format!("shim is not in an {SCOPE_PREFIX}*.scope cgroup (in {rel:?})")));
    }
    let base = Path::new("/sys/fs/cgroup").join(rel);
    let sup = base.join("supervisor");
    fs::create_dir(&sup)?;
    cg_write(&sup.join("cgroup.procs"), &std::process::id().to_string())?;
    cg_write(&base.join("cgroup.subtree_control"), "+memory +pids +cpu")?;
    let sb = base.join("sandbox");
    fs::create_dir(&sb)?;
    cg_write(&sb.join("memory.max"), &cfg.mem_bytes.to_string())?;
    match cg_write(&sb.join("memory.swap.max"), "0") {
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        r => r?,
    }
    cg_write(&sb.join("memory.oom.group"), "1")?;
    cg_write(&sb.join("pids.max"), &cfg.pids.to_string())?;
    if let Some(cpus) = &cfg.cpu_set {
        cg_write(&sb.join("cpu.max"), &format!("{} 100000", cpus.len() as u64 * 100_000))?;
    }
    Ok(Cgroup { sandbox: sb })
}

fn shim_main(cfg_path: &Path) -> i32 {
    set_cloexec(SHIM_STATUS_FD);
    let mut rep = ShimReport::default();
    let cfg: ShimConfig = match fs::read(cfg_path).map_err(|e| e.to_string()).and_then(|b| serde_json::from_slice(&b).map_err(|e| e.to_string())) {
        Ok(c) => c,
        Err(e) => {
            rep.error = Some(format!("shim config: {e}"));
            write_json_fd(SHIM_STATUS_FD, &rep);
            return 1;
        }
    };
    match shim_run(&cfg, &mut rep) {
        Ok(()) => {}
        Err(e) => rep.error = Some(e.to_string()),
    }
    write_json_fd(SHIM_STATUS_FD, &rep);
    0
}

fn shim_run(cfg: &ShimConfig, rep: &mut ShimReport) -> io::Result<()> {
    let cg = if cfg.use_cgroup { Some(setup_cgroup(cfg)?) } else { None };
    let procs_fd: Option<fs::File> = match &cg {
        Some(c) => Some(fs::OpenOptions::new().write(true).custom_flags(libc::O_CLOEXEC).open(c.sandbox.join("cgroup.procs"))?),
        None => None,
    };
    let raw_procs = procs_fd.as_ref().map(std::os::fd::AsRawFd::as_raw_fd);
    let mut cpu_mask: Option<libc::cpu_set_t> = None;
    if let Some(cpus) = &cfg.cpu_set {
        let mut set: libc::cpu_set_t = unsafe { std::mem::zeroed() };
        for &c in cpus {
            unsafe { libc::CPU_SET(c as usize, &mut set) };
        }
        cpu_mask = Some(set);
    }
    let mut cmd = Command::new(&cfg.bwrap);
    cmd.args(&cfg.bwrap_args).env_clear().stdin(Stdio::null()).process_group(0);
    unsafe {
        cmd.pre_exec(move || {
            if let Some(fd) = raw_procs {
                // Move this (child) process into the sandbox cgroup before exec.
                if libc::write(fd, b"0".as_ptr().cast(), 1) != 1 {
                    return Err(io::Error::last_os_error());
                }
            }
            if let Some(set) = &cpu_mask {
                if libc::sched_setaffinity(0, std::mem::size_of::<libc::cpu_set_t>(), set) != 0 {
                    return Err(io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }
    let start = Instant::now();
    let child = cmd.spawn()?;
    let pid = child.id() as libc::pid_t;
    drop(procs_fd);

    // done == true once the child has exited (before it is reaped), so the
    // timer can never signal a recycled pid.
    let state = Arc::new((Mutex::new((false, false)), Condvar::new())); // (done, timed_out)
    let timer = {
        let state = state.clone();
        let deadline = start + Duration::from_nanos(cfg.wall_timeout_ns);
        let kill_file = cg.as_ref().map(|c| c.sandbox.join("cgroup.kill"));
        std::thread::spawn(move || {
            let (m, cv) = &*state;
            let mut g = m.lock().unwrap();
            loop {
                if g.0 {
                    return;
                }
                let now = Instant::now();
                if now >= deadline {
                    g.1 = true;
                    if let Some(k) = &kill_file {
                        let _ = fs::write(k, "1");
                    }
                    unsafe {
                        libc::kill(pid, libc::SIGKILL);
                    }
                    return;
                }
                g = cv.wait_timeout(g, deadline - now).unwrap().0;
            }
        })
    };
    loop {
        let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
        let r = unsafe { libc::waitid(libc::P_PID, pid as libc::id_t, &mut info, libc::WEXITED | libc::WNOWAIT) };
        if r == 0 {
            break;
        }
        let e = io::Error::last_os_error();
        if e.raw_os_error() != Some(libc::EINTR) {
            return Err(e);
        }
    }
    rep.wall_ns = start.elapsed().as_nanos() as u64;
    {
        let (m, cv) = &*state;
        let mut g = m.lock().unwrap();
        g.0 = true;
        rep.timed_out = g.1;
        cv.notify_all();
    }
    let _ = timer.join();
    let mut status = 0;
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    unsafe { libc::wait4(pid, &mut status, 0, &mut ru) };
    if libc::WIFEXITED(status) {
        rep.bwrap_exit = Some(libc::WEXITSTATUS(status));
    } else if libc::WIFSIGNALED(status) {
        rep.bwrap_signal = Some(libc::WTERMSIG(status));
    }
    let tv = |t: libc::timeval| t.tv_sec as u64 * 1_000_000_000 + t.tv_usec as u64 * 1000;
    rep.utime_ns = tv(ru.ru_utime);
    rep.stime_ns = tv(ru.ru_stime);
    rep.maxrss_bytes = ru.ru_maxrss as u64 * 1024;
    std::mem::forget(child);

    if let Some(c) = &cg {
        // Belt and braces: nothing may survive in the sandbox cgroup.
        let _ = fs::write(c.sandbox.join("cgroup.kill"), "1");
        let mut s = CgroupStats { path: c.sandbox.display().to_string(), ..Default::default() };
        s.peak_bytes = cg_read(&c.sandbox.join("memory.peak")).ok().and_then(|t| t.trim().parse().ok()).unwrap_or(0);
        s.usage_ns = cg_read(&c.sandbox.join("cpu.stat")).ok().and_then(|t| cg_kv(&t, "usage_usec")).unwrap_or(0) * 1000;
        s.oom_kills = cg_read(&c.sandbox.join("memory.events")).ok().and_then(|t| cg_kv(&t, "oom_kill")).unwrap_or(0);
        s.pids_max_events = cg_read(&c.sandbox.join("pids.events")).ok().and_then(|t| cg_kv(&t, "max")).unwrap_or(0);
        rep.cgroup = Some(s);
    }
    Ok(())
}
