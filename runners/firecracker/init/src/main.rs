//! `arena-init`: PID 1 of an arena Firecracker guest.
//!
//! 1. mounts /proc, /sys, /dev, cgroup2, /dev/shm;
//! 2. reads the job from the raw control drive (`/dev/vdb`);
//! 3. builds the candidate root: a read-only overlay of a mount-point
//!    skeleton over the arena rootfs (or the job's root image, e.g. a pinned
//!    build toolchain), with the per-run scratch drive at `/scratch` (rw),
//!    `/tmp` on scratch, and every bundle drive read-only under `/in`/`/opt`;
//!    performs `copy_in` / `scratch_dirs`;
//! 4. runs argv chrooted into that root as an unprivileged uid with a
//!    cleared env and the requested cwd, in a dedicated cgroup
//!    (memory.max / pids.max / oom.group), with rlimits and
//!    `PR_SET_NO_NEW_PRIVS`; stdout/stderr go to pipes and are truncated;
//!    a guest-side timeout kills the cgroup (the host has a later hard one);
//! 5. prints `ARENA-START`/`ARENA-EXIT` markers on the serial console so the
//!    host can time the run, kills everything left in the cgroup;
//! 6. writes the report + collected output files to the raw output drive
//!    and reboots (which makes Firecracker exit).
//!
//! Init runs as root inside the guest and is part of the arena TCB; the
//! candidate never runs as root. Nothing here trusts the scratch contents.

use arena_fc_proto::{
    self as proto, CollectSummary, GuestJob, GuestReport, GuestStatus, OutWriter,
};
use std::ffi::CString;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const JOB_CG: &str = "/sys/fs/cgroup/job";

fn console(line: &str) {
    // fd 1 is /dev/console (ttyS0) for PID 1.
    let mut out = io::stdout().lock();
    let _ = writeln!(out, "{line}");
    let _ = out.flush();
}

fn cstr(s: &str) -> CString {
    CString::new(s).expect("no NUL")
}

fn mount(
    src: &str,
    target: &str,
    fstype: &str,
    flags: libc::c_ulong,
    data: &str,
) -> io::Result<()> {
    let (s, t, f, d) = (cstr(src), cstr(target), cstr(fstype), cstr(data));
    let r = unsafe {
        libc::mount(
            s.as_ptr(),
            t.as_ptr(),
            if fstype.is_empty() {
                std::ptr::null()
            } else {
                f.as_ptr()
            },
            flags,
            if data.is_empty() {
                std::ptr::null()
            } else {
                d.as_ptr() as *const libc::c_void
            },
        )
    };
    if r != 0 {
        let e = io::Error::last_os_error();
        return Err(io::Error::new(
            e.kind(),
            format!("mount {src} on {target} ({fstype}): {e}"),
        ));
    }
    Ok(())
}

fn ctx<T>(r: io::Result<T>, what: &str) -> Result<T, String> {
    r.map_err(|e| format!("{what}: {e}"))
}

fn base_mounts() -> Result<(), String> {
    let nsd = libc::MS_NOSUID | libc::MS_NODEV;
    ctx(
        mount("proc", "/proc", "proc", nsd | libc::MS_NOEXEC, "hidepid=2"),
        "proc",
    )?;
    ctx(
        mount(
            "sysfs",
            "/sys",
            "sysfs",
            nsd | libc::MS_NOEXEC | libc::MS_RDONLY,
            "",
        ),
        "sys",
    )?;
    // CONFIG_DEVTMPFS_MOUNT may already have mounted /dev.
    if let Err(e) = mount(
        "devtmpfs",
        "/dev",
        "devtmpfs",
        libc::MS_NOSUID | libc::MS_NOEXEC,
        "mode=0755",
    ) {
        if e.raw_os_error() != Some(libc::EBUSY) && !e.to_string().contains("busy") {
            return Err(format!("devtmpfs: {e}"));
        }
    }
    ctx(
        mount(
            "cgroup2",
            "/sys/fs/cgroup",
            "cgroup2",
            nsd | libc::MS_NOEXEC,
            "",
        ),
        "cgroup2",
    )?;
    let _ = fs::create_dir_all("/dev/shm");
    ctx(
        mount("tmpfs", "/dev/shm", "tmpfs", nsd, "mode=1777,size=64m"),
        "shm",
    )?;
    // Only emergencies reach the console, so kernel messages (e.g. OOM
    // reports) cannot interleave with the host-timed marker lines.
    unsafe {
        libc::klogctl(
            8, /* SYSLOG_ACTION_CONSOLE_LEVEL */
            std::ptr::null_mut(),
            1,
        )
    };
    Ok(())
}

fn read_control() -> Result<GuestJob, String> {
    let mut f = ctx(
        File::open(proto::dev_path(proto::CTL_DEV_INDEX)),
        "open control drive",
    )?;
    let mut buf = Vec::new();
    ctx(
        (&mut f)
            .take(proto::MAX_CONTROL_LEN as u64 + 4096)
            .read_to_end(&mut buf),
        "read control drive",
    )?;
    proto::decode_control(&buf)
}

const RUN: &str = "/run/arena";
/// The candidate's root: read-only overlay of SKEL (mount points) over BASE.
const ROOT: &str = "/run/arena/root";
const SKEL: &str = "/run/arena/skel";
const BASE: &str = "/run/arena/base";
const HIDDEN: &str = "/run/arena/m";

fn safe_abs(p: &str) -> Result<&str, String> {
    let rel = p
        .strip_prefix('/')
        .ok_or_else(|| format!("guest path {p:?} must be absolute"))?;
    if rel.is_empty() {
        return Ok(rel);
    }
    proto::validate_rel_path(rel)?;
    Ok(rel)
}

fn overlaps(a: &str, b: &str) -> bool {
    a == b || a.starts_with(&format!("{b}/")) || b.starts_with(&format!("{a}/"))
}

/// Read-only mount paths: under /in/ or /opt/, safe characters, no overlap
/// with scratch or with each other.
fn check_mount_path(p: &str, others: &[&str]) -> Result<(), String> {
    if !proto::GUEST_MOUNT_PREFIXES
        .iter()
        .any(|pre| p.starts_with(pre))
    {
        return Err(format!(
            "mount path {p:?} not under {:?}",
            proto::GUEST_MOUNT_PREFIXES
        ));
    }
    let rel = safe_abs(p)?;
    if !rel
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || b"._-/+".contains(&b))
    {
        return Err(format!("mount path {p:?} has unsupported characters"));
    }
    if overlaps(p, proto::GUEST_SCRATCH) || others.iter().any(|o| overlaps(o, p)) {
        return Err(format!("mount path {p:?} overlaps another mount"));
    }
    Ok(())
}

fn mkdirs(p: &str) -> Result<(), String> {
    ctx(fs::create_dir_all(p), &format!("mkdir {p}"))
}

/// Builds the candidate root at ROOT:
/// overlay(lower = SKEL : BASE) read-only, where BASE is the arena rootfs
/// (bind of `/`) or the job's root image, and SKEL only holds mount points.
/// Then proc/dev/sys, scratch (rw), /tmp (on scratch) and the read-only
/// bundles are mounted inside it.
fn setup_root(job: &GuestJob) -> Result<(), String> {
    let nsd = libc::MS_NOSUID | libc::MS_NODEV;
    let ro = nsd | libc::MS_RDONLY;
    ctx(
        mount(
            "tmpfs",
            "/run",
            "tmpfs",
            nsd | libc::MS_NOEXEC,
            "mode=0755,size=8m",
        ),
        "run",
    )?;
    for d in [ROOT, SKEL, BASE, HIDDEN] {
        mkdirs(d)?;
    }
    // base layer
    match job.root_dev_index {
        Some(i) => {
            if !(proto::FIRST_MOUNT_DEV_INDEX..26).contains(&i) {
                return Err("bad root image device".into());
            }
            ctx(
                mount(&proto::dev_path(i), BASE, "ext4", ro, "noload"),
                "root image",
            )?;
        }
        None => {
            ctx(mount("/", BASE, "", libc::MS_BIND, ""), "bind rootfs")?;
            ctx(
                mount("", BASE, "", libc::MS_BIND | libc::MS_REMOUNT | ro, ""),
                "rootfs ro",
            )?;
        }
    }
    // skeleton: every mount point the candidate root needs
    if job.mounts.len() > proto::MAX_MOUNTS {
        return Err("too many mounts".into());
    }
    let mut seen: Vec<&str> = Vec::new();
    for m in &job.mounts {
        check_mount_path(&m.guest_path, &seen)?;
        seen.push(&m.guest_path);
    }
    for d in ["proc", "sys", "dev", "tmp", "scratch"] {
        mkdirs(&format!("{SKEL}/{d}"))?;
    }
    for m in &job.mounts {
        let t = format!("{SKEL}{}", m.guest_path);
        match m.kind {
            proto::MountKind::Dir => mkdirs(&t)?,
            proto::MountKind::File { .. } => {
                mkdirs(Path::new(&t).parent().unwrap().to_str().unwrap())?;
                ctx(File::create(&t), "create file mount point")?;
            }
        }
    }
    ctx(
        mount(
            "overlay",
            ROOT,
            "overlay",
            libc::MS_NOSUID | libc::MS_RDONLY,
            &format!("lowerdir={SKEL}:{BASE}"),
        ),
        "overlay root",
    )?;
    // kernel filesystems
    ctx(
        mount(
            "proc",
            &format!("{ROOT}/proc"),
            "proc",
            nsd | libc::MS_NOEXEC,
            "hidepid=2",
        ),
        "root proc",
    )?;
    ctx(
        mount(
            "/dev",
            &format!("{ROOT}/dev"),
            "",
            libc::MS_BIND | libc::MS_REC,
            "",
        ),
        "root dev",
    )?;
    ctx(
        mount("/sys", &format!("{ROOT}/sys"), "", libc::MS_BIND, ""),
        "root sys",
    )?;
    ctx(
        mount(
            "",
            &format!("{ROOT}/sys"),
            "",
            libc::MS_BIND | libc::MS_REMOUNT | ro | libc::MS_NOEXEC,
            "",
        ),
        "root sys ro",
    )?;
    // scratch
    let scratch = format!("{ROOT}{}", proto::GUEST_SCRATCH);
    ctx(
        mount(
            &proto::dev_path(job.scratch_dev_index),
            &scratch,
            "ext4",
            nsd,
            "errors=remount-ro",
        ),
        "scratch",
    )?;
    let _ = fs::remove_dir(format!("{scratch}/lost+found"));
    chown(&scratch, proto::CANDIDATE_UID, proto::CANDIDATE_GID)?;
    let tmp = format!("{scratch}/tmp");
    mkdirs(&tmp)?;
    chown(&tmp, proto::CANDIDATE_UID, proto::CANDIDATE_GID)?;
    ctx(
        mount(&tmp, &format!("{ROOT}/tmp"), "", libc::MS_BIND, ""),
        "bind tmp",
    )?;
    // read-only bundles
    for (i, m) in job.mounts.iter().enumerate() {
        if m.dev_index < proto::FIRST_MOUNT_DEV_INDEX
            || m.dev_index >= 26
            || Some(m.dev_index) == job.root_dev_index
        {
            return Err("bad mount device".into());
        }
        let dev = proto::dev_path(m.dev_index);
        let target = format!("{ROOT}{}", m.guest_path);
        match &m.kind {
            proto::MountKind::Dir => {
                ctx(mount(&dev, &target, "ext4", ro, "noload"), "bundle mount")?
            }
            proto::MountKind::File { name } => {
                proto::validate_rel_path(name)?;
                if name.contains('/') {
                    return Err("file mount name must be a single component".into());
                }
                let hidden = format!("{HIDDEN}/{i}");
                mkdirs(&hidden)?;
                ctx(
                    mount(&dev, &hidden, "ext4", ro, "noload"),
                    "file bundle mount",
                )?;
                ctx(
                    mount(&format!("{hidden}/{name}"), &target, "", libc::MS_BIND, ""),
                    "bind file",
                )?;
                ctx(
                    mount("", &target, "", libc::MS_BIND | libc::MS_REMOUNT | ro, ""),
                    "remount file ro",
                )?;
            }
        }
    }
    let _ = RUN;
    Ok(())
}

/// Creates `rel` (scratch-relative) and its missing parents, owned by the
/// candidate.
fn mkdirs_owned(scratch: &str, rel: &str) -> Result<(), String> {
    proto::validate_rel_path(rel)?;
    let mut cur = scratch.to_string();
    for comp in rel.split('/') {
        cur = format!("{cur}/{comp}");
        match fs::symlink_metadata(&cur) {
            Ok(m) if m.is_dir() => continue,
            Ok(_) => return Err(format!("{rel}: exists and is not a directory")),
            Err(_) => {
                ctx(fs::create_dir(&cur), &format!("mkdir {rel}"))?;
                chown(&cur, proto::CANDIDATE_UID, proto::CANDIDATE_GID)?;
            }
        }
    }
    Ok(())
}

/// Copies a read-only guest tree into scratch as the candidate's property.
/// Only regular files and directories are allowed.
fn copy_into(src: &Path, dst: &Path, depth: u32) -> Result<(), String> {
    if depth > 64 {
        return Err(format!("copy_in: {} too deep", src.display()));
    }
    let md = ctx(
        fs::symlink_metadata(src),
        &format!("copy_in {}", src.display()),
    )?;
    let dst_s = dst.to_str().ok_or("non-utf8 path")?.to_string();
    if md.is_dir() {
        ctx(fs::create_dir(dst), &format!("copy_in mkdir {dst_s}"))?;
        chown(&dst_s, proto::CANDIDATE_UID, proto::CANDIDATE_GID)?;
        let mut names: Vec<_> = ctx(fs::read_dir(src), "copy_in readdir")?
            .filter_map(|e| e.ok())
            .map(|e| e.file_name())
            .collect();
        names.sort();
        for n in names {
            copy_into(&src.join(&n), &dst.join(&n), depth + 1)?;
        }
    } else if md.is_file() {
        let mut inp = ctx(
            OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_NOFOLLOW)
                .open(src),
            &format!("copy_in open {}", src.display()),
        )?;
        let mode = if md.permissions().mode() & 0o111 != 0 {
            0o755
        } else {
            0o644
        };
        let mut out = ctx(
            OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(mode)
                .open(dst),
            &format!("copy_in create {dst_s}"),
        )?;
        ctx(io::copy(&mut inp, &mut out), &format!("copy_in {dst_s}"))?;
        chown(&dst_s, proto::CANDIDATE_UID, proto::CANDIDATE_GID)?;
    } else {
        return Err(format!(
            "copy_in: {} is not a regular file or directory",
            src.display()
        ));
    }
    Ok(())
}

fn prepare_scratch(job: &GuestJob) -> Result<(), String> {
    let scratch = format!("{ROOT}{}", proto::GUEST_SCRATCH);
    for (from, to) in &job.copy_in {
        safe_abs(from)?;
        proto::validate_rel_path(to)?;
        if let Some((parent, _)) = to.rsplit_once('/') {
            mkdirs_owned(&scratch, parent)?;
        }
        copy_into(
            Path::new(&format!("{ROOT}{from}")),
            Path::new(&format!("{scratch}/{to}")),
            0,
        )?;
    }
    for d in &job.scratch_dirs {
        mkdirs_owned(&scratch, d)?;
    }
    Ok(())
}

fn chown(p: &str, uid: u32, gid: u32) -> Result<(), String> {
    let c = cstr(p);
    if unsafe { libc::lchown(c.as_ptr(), uid, gid) } != 0 {
        return Err(format!("chown {p}: {}", io::Error::last_os_error()));
    }
    Ok(())
}

fn write_file(p: &str, v: &str) -> Result<(), String> {
    fs::write(p, v).map_err(|e| format!("write {p}={v}: {e}"))
}

fn setup_cgroup(job: &GuestJob) -> Result<(), String> {
    write_file(
        "/sys/fs/cgroup/cgroup.subtree_control",
        "+memory +pids +cpu",
    )?;
    ctx(fs::create_dir(JOB_CG), "mkdir job cgroup")?;
    write_file(
        &format!("{JOB_CG}/memory.max"),
        &job.mem_limit_bytes.to_string(),
    )?;
    let _ = fs::write(format!("{JOB_CG}/memory.swap.max"), "0");
    write_file(&format!("{JOB_CG}/memory.oom.group"), "1")?;
    write_file(&format!("{JOB_CG}/pids.max"), &job.pids_max.to_string())?;
    // Memory is bounded only by the cgroup: always overcommit, so a large
    // allocation behaves as on a normal host (succeeds, then OOM-kills when
    // touched beyond memory.max) instead of failing against the VM's RAM.
    write_file("/proc/sys/vm/overcommit_memory", "1")?;
    // keep init itself out of the OOM killer's reach
    let _ = fs::write("/proc/self/oom_score_adj", "-1000");
    Ok(())
}

fn read_kv(path: &str, key: &str) -> u64 {
    fs::read_to_string(path)
        .ok()
        .and_then(|s| {
            s.lines().find_map(|l| {
                let mut it = l.split_whitespace();
                (it.next() == Some(key))
                    .then(|| it.next()?.parse().ok())
                    .flatten()
            })
        })
        .unwrap_or(0)
}

fn read_u64(path: &str) -> u64 {
    fs::read_to_string(path)
        .ok()
        .and_then(|s| s.trim().parse().ok())
        .unwrap_or(0)
}

/// Reads a pipe to EOF keeping the first `cap` bytes; returns (kept, total).
fn drain(mut r: impl Read + Send + 'static, cap: usize) -> std::thread::JoinHandle<(Vec<u8>, u64)> {
    std::thread::spawn(move || {
        let mut kept = Vec::new();
        let mut total = 0u64;
        let mut buf = [0u8; 16384];
        loop {
            match r.read(&mut buf) {
                Ok(0) => break,
                Ok(n) => {
                    total += n as u64;
                    let room = cap.saturating_sub(kept.len());
                    kept.extend_from_slice(&buf[..n.min(room)]);
                }
                Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
                Err(_) => break,
            }
        }
        (kept, total)
    })
}

struct RunResult {
    status: GuestStatus,
    wall_ns: u64,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    stdout_total: u64,
    stderr_total: u64,
}

fn run_candidate(job: &GuestJob) -> Result<RunResult, String> {
    if job.argv.is_empty() {
        return Err("empty argv".into());
    }
    let procs = cstr(&format!("{JOB_CG}/cgroup.procs"));
    let root_c = cstr(ROOT);
    safe_abs(&job.cwd)?;
    let cwd_c = cstr(&job.cwd);
    let oom_adj = cstr("/proc/self/oom_score_adj");
    let nofile = job.nofile;
    let nproc = job.pids_max as u64;
    let (uid, gid) = (proto::CANDIDATE_UID, proto::CANDIDATE_GID);

    let mut cmd = Command::new(&job.argv[0]);
    cmd.args(&job.argv[1..])
        .env_clear()
        .envs(job.env.iter().map(|(k, v)| (k, v)))
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    unsafe {
        cmd.pre_exec(move || {
            // async-signal-safe only: raw syscalls, no allocation.
            let fd = libc::open(procs.as_ptr(), libc::O_WRONLY | libc::O_CLOEXEC);
            if fd < 0 {
                return Err(io::Error::last_os_error());
            }
            let w = libc::write(fd, b"0".as_ptr() as *const libc::c_void, 1);
            libc::close(fd);
            if w != 1 {
                return Err(io::Error::last_os_error());
            }
            // init runs at -1000 (unkillable); the candidate must be an
            // ordinary OOM victim or a memcg OOM would livelock.
            let fd = libc::open(oom_adj.as_ptr(), libc::O_WRONLY | libc::O_CLOEXEC);
            if fd < 0 {
                return Err(io::Error::last_os_error());
            }
            let w = libc::write(fd, b"0".as_ptr() as *const libc::c_void, 1);
            libc::close(fd);
            if w != 1 {
                return Err(io::Error::last_os_error());
            }
            if libc::chroot(root_c.as_ptr()) != 0 || libc::chdir(cwd_c.as_ptr()) != 0 {
                return Err(io::Error::last_os_error());
            }
            let lim = |res, v: u64| {
                let rl = libc::rlimit {
                    rlim_cur: v,
                    rlim_max: v,
                };
                if libc::setrlimit(res, &rl) != 0 {
                    Err(io::Error::last_os_error())
                } else {
                    Ok(())
                }
            };
            lim(libc::RLIMIT_CORE, 0)?;
            lim(libc::RLIMIT_NOFILE, nofile)?;
            lim(libc::RLIMIT_NPROC, nproc)?;
            if libc::setsid() < 0 {
                return Err(io::Error::last_os_error());
            }
            if libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0 {
                return Err(io::Error::last_os_error());
            }
            if libc::setgroups(0, std::ptr::null()) != 0
                || libc::setresgid(gid, gid, gid) != 0
                || libc::setresuid(uid, uid, uid) != 0
            {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        });
    }

    console(&format!("{} {}", proto::MARKER_START, job.nonce));
    let t0 = Instant::now();
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            let wall_ns = t0.elapsed().as_nanos() as u64;
            console(&format!(
                "{} {} spawn-failed",
                proto::MARKER_EXIT,
                job.nonce
            ));
            return Ok(RunResult {
                status: GuestStatus::SpawnFailed {
                    error: e.to_string(),
                },
                wall_ns,
                stdout: vec![],
                stderr: vec![],
                stdout_total: 0,
                stderr_total: 0,
            });
        }
    };
    let out_t = drain(child.stdout.take().unwrap(), proto::STREAM_CAP);
    let err_t = drain(child.stderr.take().unwrap(), proto::STREAM_CAP);
    let timed_out = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let (done_tx, done_rx) = std::sync::mpsc::channel::<()>();
    let timer = {
        let timed_out = timed_out.clone();
        let limit = Duration::from_millis(job.timeout_ms);
        std::thread::spawn(move || {
            if done_rx.recv_timeout(limit.saturating_sub(t0.elapsed()))
                == Err(std::sync::mpsc::RecvTimeoutError::Timeout)
            {
                timed_out.store(true, std::sync::atomic::Ordering::SeqCst);
                let _ = fs::write(format!("{JOB_CG}/cgroup.kill"), "1");
            }
        })
    };
    let st = child.wait().map_err(|e| format!("wait: {e}"))?;
    let _ = done_tx.send(());
    let _ = timer.join();
    let wall_ns = t0.elapsed().as_nanos() as u64;
    console(&format!("{} {} {:?}", proto::MARKER_EXIT, job.nonce, st));

    // Kill anything the candidate left behind, then wait for the cgroup to
    // empty so pipes close and the scratch disk is quiescent.
    let _ = fs::write(format!("{JOB_CG}/cgroup.kill"), "1");
    let deadline = Instant::now() + Duration::from_secs(5);
    while read_kv(&format!("{JOB_CG}/cgroup.events"), "populated") != 0 && Instant::now() < deadline
    {
        std::thread::sleep(Duration::from_millis(5));
    }
    let (stdout, stdout_total) = out_t.join().unwrap_or_default();
    let (stderr, stderr_total) = err_t.join().unwrap_or_default();

    let oom = read_kv(&format!("{JOB_CG}/memory.events"), "oom_kill")
        + read_kv(&format!("{JOB_CG}/memory.events"), "oom_group_kill");
    let status = if timed_out.load(std::sync::atomic::Ordering::SeqCst) {
        GuestStatus::TimedOut
    } else if let Some(code) = st.code() {
        GuestStatus::Exited { code }
    } else {
        let sig = st.signal().unwrap_or(0);
        if sig == libc::SIGKILL && oom > 0 {
            GuestStatus::OomKilled
        } else {
            GuestStatus::Signaled { signal: sig }
        }
    };
    Ok(RunResult {
        status,
        wall_ns,
        stdout,
        stderr,
        stdout_total,
        stderr_total,
    })
}

/// Collect `job.collect` (scratch-relative files/dirs; all candidate
/// processes are dead by now). Missing paths are skipped; symlinks and
/// special files are violations.
fn collect_outputs(job: &GuestJob, w: &mut OutWriter<impl Write>) -> CollectSummary {
    let mut sum = CollectSummary {
        complete: true,
        ..Default::default()
    };
    let scratch = PathBuf::from(format!("{ROOT}{}", proto::GUEST_SCRATCH));
    // normalize: drop entries nested under another entry (no duplicates)
    let mut roots: Vec<&String> = job.collect.iter().collect();
    roots.sort();
    roots.dedup();
    let roots: Vec<&String> = roots
        .iter()
        .filter(|r| {
            !job.collect
                .iter()
                .any(|o| o != **r && r.starts_with(&format!("{o}/")))
        })
        .copied()
        .collect();
    // (path, rel, depth); processed depth-first in lexicographic order
    let mut stack: Vec<(PathBuf, String, u32)> = Vec::new();
    for r in roots.iter().rev() {
        if let Err(e) = proto::validate_rel_path(r) {
            sum.violations.push(format!("collect {r:?}: {e}"));
            sum.complete = false;
            continue;
        }
        stack.push((scratch.join(r.as_str()), r.to_string(), 0));
    }
    'walk: while let Some((path, relp, depth)) = stack.pop() {
        let md = match fs::symlink_metadata(&path) {
            Ok(m) => m,
            Err(e) if e.kind() == io::ErrorKind::NotFound && depth == 0 => continue,
            Err(err) => {
                sum.violations.push(format!("{relp}: {err}"));
                sum.complete = false;
                continue;
            }
        };
        let ft = md.file_type();
        if ft.is_dir() {
            if depth >= 32 {
                sum.violations.push(format!("{relp}: too deep"));
                sum.complete = false;
                continue;
            }
            let mut entries: Vec<_> = match fs::read_dir(&path) {
                Ok(rd) => rd.filter_map(|e| e.ok()).map(|e| e.file_name()).collect(),
                Err(e) => {
                    sum.violations.push(format!("{relp}: unreadable dir: {e}"));
                    sum.complete = false;
                    continue;
                }
            };
            entries.sort();
            for name in entries.into_iter().rev() {
                let Some(n) = name.to_str() else {
                    sum.violations
                        .push(format!("{relp}: non-utf8 name {:?}", name.as_bytes()));
                    sum.complete = false;
                    continue;
                };
                let child = format!("{relp}/{n}");
                if let Err(err) = proto::validate_rel_path(&child) {
                    sum.violations.push(format!("{child:?}: {err}"));
                    sum.complete = false;
                    continue;
                }
                stack.push((path.join(n), child, depth + 1));
            }
        } else if ft.is_file() {
            if sum.files + 1 > job.max_output_files as u64 {
                sum.violations
                    .push("output file count limit reached".into());
                sum.complete = false;
                break 'walk;
            }
            if sum.bytes + md.size() > job.max_output_bytes {
                sum.violations
                    .push(format!("{relp}: output size limit reached"));
                sum.complete = false;
                break 'walk;
            }
            let mut f = match OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
                .open(&path)
            {
                Ok(f) => f,
                Err(err) => {
                    sum.violations.push(format!("{relp}: open: {err}"));
                    sum.complete = false;
                    continue;
                }
            };
            let exec = md.permissions().mode() & 0o111 != 0;
            match w.write_file(&relp, exec, md.size(), &mut f) {
                Ok(real) => {
                    if real != md.size() {
                        sum.violations
                            .push(format!("{relp}: changed size while reading"));
                        sum.complete = false;
                    }
                    sum.files += 1;
                    sum.bytes += md.size();
                }
                Err(err) => {
                    // A failed record leaves the stream unusable; stop here.
                    sum.violations.push(format!("{relp}: {err}"));
                    sum.complete = false;
                    break 'walk;
                }
            }
        } else {
            sum.violations
                .push(format!("{relp}: not a regular file or directory"));
            sum.complete = false;
        }
    }
    sum
}

fn write_out(
    job: Option<&GuestJob>,
    report: &GuestReport,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<(), String> {
    let mut dev = ctx(
        OpenOptions::new()
            .write(true)
            .open(proto::dev_path(proto::OUT_DEV_INDEX)),
        "open output drive",
    )?;
    let dev_size = ctx(dev.seek(SeekFrom::End(0)), "size output drive")?;
    ctx(dev.seek(SeekFrom::Start(0)), "seek output drive")?;
    let limit = job.map_or(dev_size, |j| j.out_dev_bytes.min(dev_size));
    let mut w = OutWriter::new(io::BufWriter::with_capacity(1 << 20, &mut dev), limit);
    ctx(w.write_header(report, stdout, stderr), "write report")?;
    let summary = match job {
        Some(j) if !matches!(report.status, GuestStatus::InitError { .. }) => {
            collect_outputs(j, &mut w)
        }
        _ => CollectSummary::default(),
    };
    let bw = ctx(w.finish(&summary), "finish output")?;
    drop(bw);
    ctx(dev.sync_all(), "sync output drive")?;
    Ok(())
}

fn error_report(nonce: &str, error: String) -> GuestReport {
    GuestReport {
        version: proto::PROTO_VERSION,
        nonce: nonce.to_string(),
        status: GuestStatus::InitError { error },
        guest_wall_ns: 0,
        guest_cpu_ns: 0,
        guest_peak_mem_bytes: 0,
        oom_kills: 0,
        stdout_total_bytes: 0,
        stderr_total_bytes: 0,
    }
}

fn run() -> Result<(), String> {
    base_mounts()?;
    let job = match read_control() {
        Ok(j) => j,
        Err(e) => {
            write_out(None, &error_report("", format!("control: {e}")), b"", b"")?;
            return Ok(());
        }
    };
    let prep = setup_root(&job)
        .and_then(|_| prepare_scratch(&job))
        .and_then(|_| setup_cgroup(&job));
    if let Err(e) = prep {
        console(&format!("arena-init: setup failed: {e}"));
        write_out(Some(&job), &error_report(&job.nonce, e), b"", b"")?;
        return Ok(());
    }
    let res = match run_candidate(&job) {
        Ok(r) => r,
        Err(e) => {
            write_out(Some(&job), &error_report(&job.nonce, e), b"", b"")?;
            return Ok(());
        }
    };
    let report = GuestReport {
        version: proto::PROTO_VERSION,
        nonce: job.nonce.clone(),
        status: res.status,
        guest_wall_ns: res.wall_ns,
        guest_cpu_ns: read_kv(&format!("{JOB_CG}/cpu.stat"), "usage_usec") * 1000,
        guest_peak_mem_bytes: read_u64(&format!("{JOB_CG}/memory.peak")),
        oom_kills: read_kv(&format!("{JOB_CG}/memory.events"), "oom_kill"),
        stdout_total_bytes: res.stdout_total,
        stderr_total_bytes: res.stderr_total,
    };
    write_out(Some(&job), &report, &res.stdout, &res.stderr)
}

fn main() {
    if std::process::id() != 1 {
        eprintln!("arena-init must run as PID 1 inside an arena guest");
        std::process::exit(2);
    }
    let r = std::panic::catch_unwind(run);
    match r {
        Ok(Ok(())) => {}
        Ok(Err(e)) => console(&format!("arena-init: fatal: {e}")),
        Err(_) => console("arena-init: panic"),
    }
    unsafe {
        libc::sync();
        // With `reboot=k` this resets via the i8042 and Firecracker exits.
        libc::reboot(libc::RB_AUTOBOOT);
    }
    loop {
        std::thread::sleep(Duration::from_secs(1));
    }
}
