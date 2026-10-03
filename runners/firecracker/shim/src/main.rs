//! `arena-fc-shim`: PID 1 of the delivery container.
//!
//! The container is *not* the security boundary — the microVM is. The shim
//! exists because the host user cannot open /dev/kvm directly and because the
//! jailer needs root to build its chroot. It:
//!
//! 1. makes the container's (namespaced) cgroup2 tree writable, moves itself
//!    into a leaf so controllers can be delegated, and lets the jailer
//!    create `firecracker/<id>` with memory/pids/cpuset limits;
//! 2. moves the per-run images into the jail root and launches
//!    `jailer ... -- --no-api --config-file vm.json` (Firecracker's default
//!    seccomp filters stay on);
//! 3. watches the serial console for the guest's start/exit markers and
//!    timestamps them on the host clock; enforces boot/run/collect timeouts
//!    by `cgroup.kill`;
//! 4. records the VMM cgroup accounting (authoritative), moves the output
//!    image out, deletes the jail and hands everything back to the host uid.
//!
//! Usage: `arena-fc-shim run /job` | `arena-fc-shim cleanup /job`.

use arena_fc_proto::{self as proto, HostCgroupStats, ShimJob, ShimResult, ShimStatus};
use std::ffi::CString;
use std::fs;
use std::io::{self, BufRead, BufReader, Read};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

const JAILER: &str = "/usr/local/bin/jailer";
const FIRECRACKER: &str = "/usr/local/bin/firecracker";
const CG: &str = "/sys/fs/cgroup";
const JAIL_BASE: &str = "jail";

fn cstr(s: &str) -> CString {
    CString::new(s).unwrap()
}

fn chown_path(p: &Path, uid: u32, gid: u32) -> io::Result<()> {
    let c = cstr(p.to_str().unwrap());
    if unsafe { libc::lchown(c.as_ptr(), uid, gid) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

fn chown_tree(p: &Path, uid: u32, gid: u32) -> io::Result<()> {
    let md = fs::symlink_metadata(p)?;
    chown_path(p, uid, gid)?;
    if md.is_dir() {
        for e in fs::read_dir(p)? {
            chown_tree(&e?.path(), uid, gid)?;
        }
    }
    Ok(())
}

/// lchown every *directory* under `p` (files may be hardlinks of shared
/// host files and must keep their owner).
fn chown_dirs(p: &Path, uid: u32, gid: u32) -> io::Result<()> {
    let md = fs::symlink_metadata(p)?;
    if md.is_dir() {
        chown_path(p, uid, gid)?;
        for e in fs::read_dir(p)? {
            chown_dirs(&e?.path(), uid, gid)?;
        }
    }
    Ok(())
}

fn setup_cgroups() -> Result<(), String> {
    let (s, t) = (cstr(""), cstr(CG));
    let flags = libc::MS_REMOUNT | libc::MS_NOSUID | libc::MS_NODEV | libc::MS_NOEXEC;
    if unsafe {
        libc::mount(
            s.as_ptr(),
            t.as_ptr(),
            std::ptr::null(),
            flags,
            std::ptr::null(),
        )
    } != 0
    {
        return Err(format!("remount {CG} rw: {}", io::Error::last_os_error()));
    }
    let leaf = format!("{CG}/shim");
    fs::create_dir_all(&leaf).map_err(|e| format!("mkdir {leaf}: {e}"))?;
    fs::write(format!("{leaf}/cgroup.procs"), "0")
        .map_err(|e| format!("move shim into leaf: {e}"))?;
    fs::write(
        format!("{CG}/cgroup.subtree_control"),
        "+cpuset +cpu +memory +pids",
    )
    .map_err(|e| format!("enable controllers: {e}"))?;
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

fn valid_id(id: &str) -> bool {
    !id.is_empty() && id.len() <= 60 && id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
}

fn valid_file_name(n: &str) -> bool {
    !n.is_empty()
        && n.len() <= 64
        && n.bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b))
        && !n.starts_with('.')
}

struct Serial {
    tail: Vec<u8>,
    start: Option<Instant>,
    exit: Option<Instant>,
}

fn watch_serial(
    r: impl Read + Send + 'static,
    nonce: String,
    cap: usize,
    st: Arc<Mutex<Serial>>,
) -> std::thread::JoinHandle<()> {
    std::thread::spawn(move || {
        let start_m = format!("{} {}", proto::MARKER_START, nonce);
        let exit_m = format!("{} {}", proto::MARKER_EXIT, nonce);
        let mut r = BufReader::with_capacity(1 << 16, r);
        let mut line = Vec::new();
        loop {
            line.clear();
            // bounded line read: a guest cannot make us buffer unboundedly
            let n = match (&mut r).take(8192).read_until(b'\n', &mut line) {
                Ok(0) => break,
                Ok(n) => n,
                Err(_) => break,
            };
            let now = Instant::now();
            let text = String::from_utf8_lossy(&line[..n]);
            let t = text.trim_end();
            let mut s = st.lock().unwrap();
            // markers must start the line (kernel messages are prefixed)
            if s.start.is_none() && (t == start_m) {
                s.start = Some(now);
            } else if s.start.is_some() && s.exit.is_none() && t.starts_with(&exit_m) {
                s.exit = Some(now);
            }
            s.tail.extend_from_slice(&line[..n]);
            if s.tail.len() > cap {
                let cut = s.tail.len() - cap;
                s.tail.drain(..cut);
            }
        }
    })
}

fn kill_vm(cg: &str, child: &mut Child) {
    let _ = fs::write(format!("{cg}/cgroup.kill"), "1");
    let _ = child.kill();
}

fn vm_config(job: &ShimJob) -> serde_json::Value {
    let drives: Vec<_> = job
        .drives
        .iter()
        .map(|d| {
            let mut v = serde_json::json!({
                "drive_id": d.drive_id,
                "path_on_host": d.file,
                "is_root_device": d.is_root,
                "is_read_only": d.read_only,
                "cache_type": "Unsafe",
                "io_engine": "Sync",
            });
            if let Some(rl) = &d.rate_limit {
                v["rate_limiter"] = rl.to_firecracker_json();
            }
            v
        })
        .collect();
    serde_json::json!({
        "boot-source": { "kernel_image_path": job.kernel_file, "boot_args": job.boot_args },
        "drives": drives,
        "machine-config": { "vcpu_count": job.vcpus, "mem_size_mib": job.guest_mem_mib, "smt": false },
        // no "network-interfaces", no "vsock": the guest has no I/O channel
        // besides its block devices and the serial console.
    })
}

fn run(jobdir: &Path) -> Result<ShimResult, String> {
    let job: ShimJob = serde_json::from_slice(
        &fs::read(jobdir.join(proto::SHIM_JOB_FILE)).map_err(|e| format!("read job: {e}"))?,
    )
    .map_err(|e| format!("parse job: {e}"))?;
    if job.version != proto::PROTO_VERSION || !valid_id(&job.id) {
        return Err("bad job".into());
    }
    // Take ownership of the job directories (CAP_CHOWN) instead of holding
    // CAP_DAC_OVERRIDE; files are untouched (kernel/rootfs/bundles are
    // hardlinks of shared host files). Everything is chowned back at the end.
    for d in [jobdir.to_path_buf(), jobdir.join(proto::SHIM_INPUT_DIR)] {
        chown_path(&d, 0, 0).map_err(|e| format!("chown {}: {e}", d.display()))?;
    }
    setup_cgroups()?;

    // jail root: <base>/firecracker/<id>/root (jailer convention)
    let base = jobdir.join(JAIL_BASE);
    let root = base.join("firecracker").join(&job.id).join("root");
    fs::create_dir_all(&root).map_err(|e| format!("mkdir jail: {e}"))?;
    let input = jobdir.join(proto::SHIM_INPUT_DIR);
    let mut files = vec![job.kernel_file.clone()];
    files.extend(job.drives.iter().map(|d| d.file.clone()));
    for f in &files {
        if !valid_file_name(f) {
            return Err(format!("bad file name {f:?}"));
        }
        fs::rename(input.join(f), root.join(f)).map_err(|e| format!("move {f} into jail: {e}"))?;
    }
    for d in &job.drives {
        let p = root.join(&d.file);
        if d.chown_to_vmm {
            // the host created it 0600; the shim holds no CAP_FOWNER to chmod
            let mode = fs::metadata(&p)
                .map_err(|e| format!("stat {}: {e}", d.file))?
                .permissions()
                .mode();
            if mode & 0o077 != 0 {
                return Err(format!(
                    "writable drive {} has mode {mode:o}, want 0600",
                    d.file
                ));
            }
            chown_path(&p, job.vmm_uid, job.vmm_gid)
                .map_err(|e| format!("chown {}: {e}", d.file))?;
        } else {
            // shared read-only images stay owned by the host user, 0444
            let mode = fs::metadata(&p)
                .map_err(|e| format!("stat {}: {e}", d.file))?
                .permissions()
                .mode();
            if mode & 0o222 != 0 {
                return Err(format!(
                    "read-only drive {} is writable (mode {mode:o})",
                    d.file
                ));
            }
        }
    }
    fs::write(
        root.join("vm.json"),
        serde_json::to_vec_pretty(&vm_config(&job)).unwrap(),
    )
    .map_err(|e| format!("write vm.json: {e}"))?;

    let mut args: Vec<String> = vec![
        "--id".into(),
        job.id.clone(),
        "--exec-file".into(),
        FIRECRACKER.into(),
        "--uid".into(),
        job.vmm_uid.to_string(),
        "--gid".into(),
        job.vmm_gid.to_string(),
        "--chroot-base-dir".into(),
        base.to_str().unwrap().into(),
        "--cgroup-version".into(),
        "2".into(),
        "--cgroup".into(),
        format!("memory.max={}", job.vmm_mem_max_bytes),
        "--cgroup".into(),
        "memory.swap.max=0".into(),
        "--cgroup".into(),
        format!("pids.max={}", job.vmm_pids_max),
        "--resource-limit".into(),
        format!("fsize={}", job.vmm_fsize_limit),
        "--resource-limit".into(),
        "no-file=256".into(),
    ];
    if let Some(cs) = &job.cpuset {
        if !cs
            .bytes()
            .all(|b| b.is_ascii_digit() || b == b',' || b == b'-')
        {
            return Err("bad cpuset".into());
        }
        args.extend([
            "--cgroup".into(),
            format!("cpuset.cpus={cs}"),
            "--cgroup".into(),
            "cpuset.mems=0".into(),
        ]);
    }
    args.extend([
        "--".into(),
        "--no-api".into(),
        "--config-file".into(),
        "vm.json".into(),
        "--level".into(),
        "Warning".into(),
    ]);

    let cg = format!("{CG}/firecracker/{}", job.id);
    let serial = Arc::new(Mutex::new(Serial {
        tail: Vec::new(),
        start: None,
        exit: None,
    }));
    let t0 = Instant::now();
    let mut child = Command::new(JAILER)
        .args(&args)
        .env_clear()
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("spawn jailer: {e}"))?;
    let cap = job.serial_cap_bytes as usize;
    let w1 = watch_serial(
        child.stdout.take().unwrap(),
        job.nonce.clone(),
        cap,
        serial.clone(),
    );
    let w2 = watch_serial(
        child.stderr.take().unwrap(),
        job.nonce.clone(),
        cap,
        serial.clone(),
    );

    let boot_to = Duration::from_millis(job.boot_timeout_ms);
    let run_to = Duration::from_millis(job.run_timeout_ms);
    let collect_to = Duration::from_millis(job.collect_timeout_ms);
    let mut forced: Option<ShimStatus> = None;
    let mut killed_at: Option<Instant> = None;
    let exit_status = loop {
        if let Some(st) = child.try_wait().map_err(|e| format!("wait: {e}"))? {
            break st;
        }
        let now = Instant::now();
        if forced.is_none() {
            let s = serial.lock().unwrap();
            let verdict = match (s.start, s.exit) {
                (None, _) if now - t0 > boot_to => Some(ShimStatus::BootTimeout),
                (Some(st), None) if now - st > run_to => Some(ShimStatus::TimedOut),
                (Some(_), Some(ex)) if now - ex > collect_to => Some(ShimStatus::CollectTimeout),
                _ => None,
            };
            drop(s);
            if let Some(v) = verdict {
                kill_vm(&cg, &mut child);
                forced = Some(v);
                killed_at = Some(now);
            }
        }
        std::thread::sleep(Duration::from_millis(1));
    };
    let t_end = Instant::now();
    let _ = w1.join();
    let _ = w2.join();

    let cgroup = HostCgroupStats {
        memory_peak_bytes: read_u64(&format!("{cg}/memory.peak")),
        cpu_usage_ns: read_kv(&format!("{cg}/cpu.stat"), "usage_usec") * 1000,
        oom_kill: read_kv(&format!("{cg}/memory.events"), "oom_kill"),
        pids_peak: read_u64(&format!("{cg}/pids.peak")),
    };
    let _ = fs::remove_dir(&cg);
    let _ = fs::remove_dir(format!("{CG}/firecracker"));

    let s = serial.lock().unwrap();
    let boot_ns = s.start.map(|t| (t - t0).as_nanos() as u64);
    let run_wall_ns = match (s.start, s.exit, killed_at) {
        (Some(a), Some(b), _) => Some((b - a).as_nanos() as u64),
        (Some(a), None, Some(k)) => Some((k - a).as_nanos() as u64),
        _ => None,
    };
    let teardown_ns = s.exit.map(|e| (t_end - e).as_nanos() as u64);
    let serial_tail = String::from_utf8_lossy(&s.tail).into_owned();
    drop(s);

    // The jailer hands the chroot to the VMM uid; reclaim the directories
    // (CAP_CHOWN) so the shim can move the output out and delete the jail.
    chown_dirs(&base, 0, 0).map_err(|e| format!("reclaim jail: {e}"))?;
    // hand the output image back, destroy everything else from the jail
    let out_name = job
        .drives
        .iter()
        .find(|d| d.drive_id == "out")
        .map(|d| d.file.clone());
    if let Some(out) = out_name {
        let dst = jobdir.join(proto::SHIM_OUT_IMAGE);
        fs::rename(root.join(&out), &dst).map_err(|e| format!("move out image: {e}"))?;
        chown_path(&dst, job.host_uid, job.host_gid).map_err(|e| e.to_string())?;
    }
    fs::remove_dir_all(&base).map_err(|e| format!("remove jail: {e}"))?;

    let status = forced.unwrap_or(ShimStatus::VmmExited {
        code: exit_status.code(),
        signal: std::os::unix::process::ExitStatusExt::signal(&exit_status),
    });
    Ok(ShimResult {
        version: proto::PROTO_VERSION,
        status,
        vmm_wall_ns: (t_end - t0).as_nanos() as u64,
        boot_ns,
        run_wall_ns,
        teardown_ns,
        cgroup,
        serial_tail,
    })
}

fn cleanup(jobdir: &Path, uid: u32, gid: u32) -> Result<(), String> {
    let base = jobdir.join(JAIL_BASE);
    if base.exists() {
        chown_dirs(&base, 0, 0).map_err(|e| format!("reclaim jail: {e}"))?;
        fs::remove_dir_all(&base).map_err(|e| format!("remove jail: {e}"))?;
    }
    chown_tree(jobdir, uid, gid).map_err(|e| format!("chown job dir: {e}"))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (mode, jobdir) = match args.as_slice() {
        [_, m, d] => (m.as_str(), PathBuf::from(d)),
        [_, m, d, _, _] if m == "cleanup" => (m.as_str(), PathBuf::from(d)),
        _ => {
            eprintln!("usage: arena-fc-shim run <jobdir> | cleanup <jobdir> <uid> <gid>");
            std::process::exit(2);
        }
    };
    match mode {
        "run" => {
            let (uid, gid) = fs::read(jobdir.join(proto::SHIM_JOB_FILE))
                .ok()
                .and_then(|b| serde_json::from_slice::<ShimJob>(&b).ok())
                .map(|j| (j.host_uid, j.host_gid))
                .unwrap_or((0, 0));
            let res = run(&jobdir).unwrap_or_else(|error| ShimResult {
                version: proto::PROTO_VERSION,
                status: ShimStatus::Error { error },
                vmm_wall_ns: 0,
                boot_ns: None,
                run_wall_ns: None,
                teardown_ns: None,
                cgroup: HostCgroupStats::default(),
                serial_tail: String::new(),
            });
            let failed = matches!(res.status, ShimStatus::Error { .. });
            if failed {
                // never leave root-owned debris in the host's job dir
                let _ = chown_dirs(&jobdir.join(JAIL_BASE), 0, 0);
                let _ = fs::remove_dir_all(jobdir.join(JAIL_BASE));
            }
            let out = jobdir.join(proto::SHIM_RESULT_FILE);
            if let Err(e) = fs::write(&out, serde_json::to_vec_pretty(&res).unwrap()) {
                eprintln!("write result: {e}");
                std::process::exit(1);
            }
            let _ = chown_tree(&jobdir, uid, gid);
            std::process::exit(if failed { 1 } else { 0 });
        }
        "cleanup" => {
            let uid = args[3].parse().unwrap_or(0);
            let gid = args[4].parse().unwrap_or(0);
            if let Err(e) = cleanup(&jobdir, uid, gid) {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
        _ => std::process::exit(2),
    }
}
