//! End-to-end tests that boot real Firecracker microVMs.
//!
//! Gated: run with `ARENA_FC_TESTS=1` after `deploy/images/firecracker/fetch.sh`,
//! `deploy/images/rootfs/build.sh` and `deploy/images/fc-runner/build.sh`.
//! Set `ARENA_FC_TESTS_VERBOSE=1` to print per-run timings.

use arena_firecracker::*;
use sha2::{Digest as _, Sha256};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::Duration;

fn enabled() -> bool {
    std::env::var("ARENA_FC_TESTS").as_deref() == Ok("1")
}

macro_rules! gate {
    () => {
        if !enabled() {
            eprintln!("skipped: set ARENA_FC_TESTS=1");
            return;
        }
    };
}

fn deps() -> PathBuf {
    std::env::var_os("ARENA_FC_DEPS")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/data/illia/nearproof-deps/firecracker"))
}

fn sandbox() -> &'static FirecrackerSandbox {
    static SB: OnceLock<FirecrackerSandbox> = OnceLock::new();
    SB.get_or_init(|| {
        let work = deps().join("work-tests");
        let cfg = FirecrackerConfig::from_deps_dir(&deps(), &work).expect("config");
        FirecrackerSandbox::new(cfg).expect("sandbox prerequisites")
    })
}

fn scratch_dir() -> tempfile::TempDir {
    let base = deps().join("work-tests");
    fs::create_dir_all(&base).unwrap();
    tempfile::tempdir_in(base).unwrap()
}

fn spec(script: &str, out: &Path) -> RunRequest {
    let mut r = RunRequest::new(
        sandbox().rootfs_digest().clone(),
        vec!["/bin/sh".into(), "-c".into(), script.into()],
        out.to_path_buf(),
    );
    r.wall_timeout = Duration::from_secs(20);
    r.max_output_bytes = u64::MAX;
    r
}

fn run(s: &RunRequest) -> SandboxOutcome {
    let o = sandbox().run_native(s).expect("sandbox run");
    if std::env::var("ARENA_FC_TESTS_VERBOSE").is_ok() {
        let d = &o.diagnostics;
        eprintln!(
            "exit={:?} wall={:.1}ms boot={:.1}ms vmm={:.1}ms teardown={:.1}ms total={:.1}ms host_cpu={:.1}ms host_peak={}MiB guest_peak={:?}",
            o.exit,
            o.wall_ns as f64 / 1e6,
            d.boot_ns.unwrap_or(0) as f64 / 1e6,
            d.vmm_wall_ns as f64 / 1e6,
            d.teardown_ns.unwrap_or(0) as f64 / 1e6,
            d.total_ns as f64 / 1e6,
            o.cpu_ns as f64 / 1e6,
            o.peak_rss_bytes >> 20,
            d.guest_peak_mem_bytes.map(|b| b >> 20),
        );
    }
    o
}

fn stdout(o: &SandboxOutcome) -> String {
    String::from_utf8_lossy(&o.stdout_trunc).into_owned()
}

#[test]
fn hello_world() {
    gate!();
    let t = scratch_dir();
    let o = run(&spec(
        "echo hello; echo oops >&2; id -u; pwd",
        &t.path().join("out"),
    ));
    assert_eq!(o.exit, Exit::Exited(0), "{o:?}");
    assert_eq!(stdout(&o), "hello\n1000\n/scratch\n");
    assert_eq!(o.stderr_trunc, b"oops\n");
    assert!(o.diagnostics.boot_ns.is_some());
    assert!(o.cpu_ns > 0 && o.peak_rss_bytes > 0);
}

#[test]
fn exit_codes_and_signals() {
    gate!();
    let t = scratch_dir();
    assert_eq!(
        run(&spec("exit 3", &t.path().join("a"))).exit,
        Exit::Exited(3)
    );
    assert_eq!(
        run(&spec("exit 1", &t.path().join("b"))).exit,
        Exit::Exited(1)
    );
    assert_eq!(
        run(&spec("kill -SEGV $$", &t.path().join("c"))).exit,
        Exit::Signaled(11)
    );
    let mut s = spec("", &t.path().join("d"));
    s.argv = vec!["/nonexistent/prove".into()];
    let o = run(&s);
    assert_eq!(o.exit, Exit::ExecFailed);
    assert!(String::from_utf8_lossy(&o.stderr_trunc).contains("failed to execute"));
}

#[test]
fn timeout_kills_vm() {
    gate!();
    let t = scratch_dir();
    let mut s = spec("echo started; sleep 60", &t.path().join("out"));
    s.wall_timeout = Duration::from_secs(2);
    let start = std::time::Instant::now();
    let o = run(&s);
    let elapsed = start.elapsed();
    assert_eq!(o.exit, Exit::TimedOut);
    assert!(
        o.wall_ns >= 2_000_000_000 && o.wall_ns < 2_200_000_000,
        "wall {}",
        o.wall_ns
    );
    assert!(
        elapsed < Duration::from_secs(10),
        "host elapsed {elapsed:?}"
    );
    assert!(o.outputs.is_empty());
}

#[test]
fn guest_memory_limit_ooms() {
    gate!();
    let t = scratch_dir();
    // one large allocation (bigger than the VM's RAM) and incremental growth
    for (i, prog) in [
        r#"$x = "a" x (400*1024*1024); print length($x), "\n""#,
        r#"my @a; push @a, "b" x (1<<20) for 1..400; print scalar(@a), "\n""#,
    ]
    .iter()
    .enumerate()
    {
        let mut s = spec(
            &format!("exec perl -e '{prog}'"),
            &t.path().join(format!("out{i}")),
        );
        s.mem_bytes = 128 << 20;
        let o = run(&s);
        assert_eq!(o.exit, Exit::OomKilled, "{o:?}");
        assert_eq!(
            o.diagnostics.host_oom_kills, 0,
            "the guest limit, not the host one, must fire"
        );
    }
    // the same program fits with a larger limit
    let mut s2 = spec(
        r#"exec perl -e '$x = "a" x (40*1024*1024); print length($x), "\n"'"#,
        &t.path().join("out2"),
    );
    s2.mem_bytes = 256 << 20;
    let o2 = run(&s2);
    assert_eq!(o2.exit, Exit::Exited(0));
    assert_eq!(stdout(&o2), "41943040\n");
    let gp = o2.diagnostics.guest_peak_mem_bytes.unwrap();
    assert!((40 << 20..256 << 20).contains(&gp), "guest peak {gp}");
}

#[test]
fn no_network_interfaces_besides_lo() {
    gate!();
    let t = scratch_dir();
    let o = run(&spec(
        "ls /sys/class/net; echo ---; tail -n +3 /proc/net/dev | cut -d: -f1 | tr -d ' '; echo ---; \
         cat /sys/bus/virtio/devices/*/device | sort | uniq -c | tr -s ' '; echo ---; \
         ls /dev | grep -E '^(vhost|net|tun|kvm)' || echo none",
        &t.path().join("out"),
    ));
    assert_eq!(o.exit, Exit::Exited(0));
    // virtio device id 0x0002 = block; no 0x0001 (net) or 0x0013 (vsock)
    assert_eq!(stdout(&o), "lo\n---\nlo\n---\n 4 0x0002\n---\nnone\n");
}

#[test]
fn cannot_see_host_filesystem() {
    gate!();
    let t = scratch_dir();
    let marker = format!("/data/illia/arena-host-marker-{}", std::process::id());
    let o = run(&spec(
        &format!(
            "test -e {marker} && echo HOST_VISIBLE; test -e /data && echo DATA; test -e /home/illia && echo HOME; \
             test -e /var/run/docker.sock && echo DOCKER; test -e /usr/local/bin/firecracker && echo FC; \
             cat /dev/vda >/dev/null 2>&1 && echo RAW_DISK; cat /dev/vdc >/dev/null 2>&1 && echo OUT_DEV; \
             touch /etc/x 2>/dev/null && echo ROOT_WRITABLE; touch /in/x /opt/x /x 2>/dev/null && echo ROOT2_WRITABLE; \
             grep -c . /proc/mounts >/dev/null; ls /proc | grep -E '^[0-9]+$' | wc -l; echo done"
        ),
        &t.path().join("out"),
    ));
    assert_eq!(o.exit, Exit::Exited(0));
    let out = stdout(&o);
    // hidepid=2: the candidate sees only its own processes (sh, ls, grep, wc)
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.last(), Some(&"done"), "{out}");
    assert_eq!(lines.len(), 2, "unexpected visibility: {out}");
    let nprocs: u32 = lines[0].trim().parse().unwrap();
    assert!(nprocs <= 6, "candidate sees {nprocs} pids");
}

#[test]
fn env_is_cleared_and_allowlisted() {
    gate!();
    let t = scratch_dir();
    let mut s = spec("env | sort", &t.path().join("out"));
    s.env = vec![("RUST_LOG".into(), "info".into())];
    let o = run(&s);
    assert_eq!(
        stdout(&o),
        "HOME=/scratch\nLANG=C.UTF-8\nPATH=/usr/local/bin:/usr/bin:/bin\nPWD=/scratch\nRUST_LOG=info\nTMPDIR=/tmp\nTZ=UTC\n"
    );
    let mut bad = spec("true", &t.path().join("out2"));
    bad.env = vec![("LD_PRELOAD".into(), "/x.so".into())];
    assert!(matches!(
        sandbox().run_native(&bad),
        Err(InfraError::InvalidSpec(_))
    ));
}

#[test]
fn outputs_retrieved_with_digests_and_policy() {
    gate!();
    let t = scratch_dir();
    let out = t.path().join("res");
    let o = run(&spec(
        "cd out && mkdir -p sub/deeper && printf 'claim' > claim.bin && head -c 300000 /dev/urandom > sub/proof.bin && \
         printf '#!/bin/sh\\necho hi\\n' > sub/deeper/tool && chmod +x sub/deeper/tool && ln -s /etc/passwd link && \
         mkfifo fifo && echo ok",
        &out,
    ));
    assert_eq!(o.exit, Exit::Exited(0), "{o:?}");
    let paths: Vec<&str> = o.outputs.iter().map(|(p, _)| p.as_str()).collect();
    assert_eq!(
        paths,
        vec!["out/claim.bin", "out/sub/deeper/tool", "out/sub/proof.bin"]
    ); // sorted
    for (p, d) in &o.outputs {
        let bytes = fs::read(out.join(p)).unwrap();
        assert_eq!(d.hex(), hex::encode(Sha256::digest(&bytes)), "{p}");
    }
    assert_eq!(fs::read(out.join("out/claim.bin")).unwrap(), b"claim");
    assert_eq!(
        fs::metadata(out.join("out/sub/proof.bin")).unwrap().len(),
        300000
    );
    assert_eq!(
        fs::metadata(out.join("out/sub/deeper/tool"))
            .unwrap()
            .permissions()
            .mode()
            & 0o777,
        0o755
    );
    assert!(!out.join("out/link").exists() && fs::symlink_metadata(out.join("out/link")).is_err());
    assert!(!o.diagnostics.outputs_complete);
    assert_eq!(
        o.diagnostics.output_violations.len(),
        2,
        "{:?}",
        o.diagnostics.output_violations
    );
}

#[test]
fn ro_bundle_mounts() {
    gate!();
    let t = scratch_dir();
    let bundle = t.path().join("bundle");
    fs::create_dir_all(bundle.join("out")).unwrap();
    fs::write(
        bundle.join("out/prove"),
        "#!/bin/sh\necho \"proving $1\"\nexit 0\n",
    )
    .unwrap();
    fs::set_permissions(bundle.join("out/prove"), fs::Permissions::from_mode(0o755)).unwrap();
    fs::write(bundle.join("data.txt"), "params").unwrap();
    let req = t.path().join("request.bin");
    fs::write(&req, b"REQ").unwrap();
    let mut s = spec(
        "/in/bundle/out/prove x && cat /in/bundle/data.txt && echo && cat /in/request.bin && echo && \
         (touch /in/bundle/new 2>/dev/null && echo WRITABLE || echo ro) && \
         (echo y > /in/request.bin 2>/dev/null && echo WRITABLE || echo ro)",
        &t.path().join("out"),
    );
    s.ro_mounts = vec![
        RoMount {
            host_path: bundle.clone(),
            guest_path: "/in/bundle".into(),
        },
        RoMount {
            host_path: req,
            guest_path: "/in/request.bin".into(),
        },
    ];
    let o = run(&s);
    assert_eq!(o.exit, Exit::Exited(0), "{o:?}");
    assert_eq!(stdout(&o), "proving x\nparams\nREQ\nro\nro\n");
    // symlinks in a bundle are refused before anything boots
    std::os::unix::fs::symlink("/etc/passwd", bundle.join("evil")).unwrap();
    assert!(matches!(
        sandbox().run_native(&s),
        Err(InfraError::InvalidSpec(_))
    ));
}

#[test]
fn no_state_across_runs() {
    gate!();
    let t = scratch_dir();
    let o1 = run(&spec(
        "echo a > /scratch/persist; echo b > /tmp/persist; echo c > /dev/shm/persist; echo ok",
        &t.path().join("o1"),
    ));
    assert_eq!(stdout(&o1), "ok\n");
    let o2 = run(&spec("ls -A /scratch /tmp /dev/shm", &t.path().join("o2")));
    assert_eq!(stdout(&o2), "/dev/shm:\n\n/scratch:\nout\ntmp\n\n/tmp:\n");
}

#[test]
fn pids_limit_bounds_fork_bombs() {
    gate!();
    let t = scratch_dir();
    let mut s = spec(
        "i=0; while [ $i -lt 200 ]; do sleep 5 & i=$((i+1)); done 2>/dev/null; echo spawned",
        &t.path().join("out"),
    );
    s.pids = 16;
    s.wall_timeout = Duration::from_secs(15);
    let o = run(&s);
    // the shell survives fork failures; background sleeps are killed at exit
    assert!(matches!(o.exit, Exit::Exited(_)), "{o:?}");
    assert!(
        o.wall_ns < 5_000_000_000,
        "children must not outlive the candidate: {}",
        o.wall_ns
    );
}

#[test]
fn timing_sanity() {
    gate!();
    let t = scratch_dir();
    let mut walls = Vec::new();
    for i in 0..3 {
        let o = run(&spec("sleep 1", &t.path().join(format!("o{i}"))));
        assert_eq!(o.exit, Exit::Exited(0));
        walls.push(o.wall_ns);
        let boot = o.diagnostics.boot_ns.unwrap();
        assert!(boot < 5_000_000_000, "boot {boot}");
        assert!(o.diagnostics.vmm_wall_ns > o.wall_ns);
        let g = o.diagnostics.guest_wall_ns.unwrap();
        // host marker interval and guest clock agree within 50 ms
        assert!(
            (o.wall_ns as i64 - g as i64).abs() < 50_000_000,
            "host {} guest {g}",
            o.wall_ns
        );
    }
    for w in walls {
        assert!(
            (1_000_000_000..1_150_000_000).contains(&w),
            "sleep 1 measured {w}ns"
        );
    }
    // multi-vCPU pinned run: 2 busy loops on 2 vCPUs take ~1s wall, ~2s cpu
    let mut s = spec("for i in 1 2; do (end=$(($(date +%s)+1)); while [ $(date +%s) -lt $end ]; do :; done) & done; wait; nproc", &t.path().join("mc"));
    s.cpu_set = vec![2, 3];
    let o = run(&s);
    assert_eq!(stdout(&o), "2\n");
}

#[test]
fn candidate_cannot_reach_privileged_channels() {
    gate!();
    let t = scratch_dir();
    // console/kmsg would let it forge timing markers; block devices would let
    // it forge the report; cgroup files would let it lift its own limits.
    let o = run(&spec(
        "for f in /dev/console /dev/ttyS0 /dev/kmsg /dev/vda /dev/vdb /dev/vdc /dev/vdd \
                  /sys/fs/cgroup/job/memory.max /sys/fs/cgroup/job/pids.max /sys/fs/cgroup/cgroup.procs \
                  /proc/sysrq-trigger /proc/sys/kernel/panic; do \
           (printf 'ARENA-EXIT forged\\n' > $f) 2>/dev/null && echo \"WROTE $f\"; done; \
         cat /proc/1/environ >/dev/null 2>&1 && echo INIT_ENV; \
         grep -q 'NoNewPrivs:[[:space:]]*1' /proc/self/status && echo nnp; \
         grep '^CapEff' /proc/self/status; echo done",
        &t.path().join("out"),
    ));
    assert_eq!(o.exit, Exit::Exited(0));
    assert_eq!(stdout(&o), "nnp\nCapEff:\t0000000000000000\ndone\n");
}

#[test]
fn concurrent_runs_are_isolated() {
    gate!();
    let t = scratch_dir();
    let base = t.path().to_path_buf();
    let handles: Vec<_> = (0..6)
        .map(|i| {
            let out = base.join(format!("o{i}"));
            std::thread::spawn(move || {
                let o = run(&spec(
                    &format!("echo {i} > out/id; sleep 1; ls /scratch/out; cat out/id"),
                    &out,
                ));
                (i, o)
            })
        })
        .collect();
    for h in handles {
        let (i, o) = h.join().unwrap();
        assert_eq!(o.exit, Exit::Exited(0));
        assert_eq!(stdout(&o), format!("id\n{i}\n"));
        assert_eq!(o.outputs.len(), 1);
    }
}

#[test]
fn copy_in_scratch_dirs_cwd_and_collect() {
    gate!();
    let t = scratch_dir();
    let pkg = t.path().join("pkg");
    fs::create_dir_all(pkg.join("src")).unwrap();
    fs::write(pkg.join("src/a.txt"), "A").unwrap();
    fs::write(
        pkg.join("build.sh"),
        "#!/bin/sh\nmkdir -p out && cat src/a.txt > out/prove && chmod +x out/prove\n",
    )
    .unwrap();
    fs::set_permissions(pkg.join("build.sh"), fs::Permissions::from_mode(0o755)).unwrap();
    let res = t.path().join("res");
    let mut s = spec("pwd; ./build.sh && echo more >> src/a.txt && id -un 2>/dev/null; ls -ld /scratch/out/public | cut -c1-10; echo junk > /scratch/junk", &res);
    s.ro_mounts = vec![RoMount {
        host_path: pkg,
        guest_path: "/in/pkg".into(),
    }];
    s.copy_in = vec![("/in/pkg".into(), "work".into())];
    s.scratch_dirs = vec!["out/public".into()];
    s.cwd = "/scratch/work".into();
    s.collect = vec!["work/out".into(), "work/src".into(), "missing".into()];
    let o = run(&s);
    assert_eq!(o.exit, Exit::Exited(0), "{o:?}");
    assert_eq!(stdout(&o), "/scratch/work\narena\ndrwxr-xr-x\n");
    let paths: Vec<&str> = o.outputs.iter().map(|(p, _)| p.as_str()).collect();
    assert_eq!(paths, vec!["work/out/prove", "work/src/a.txt"]);
    assert_eq!(
        fs::read_to_string(res.join("work/src/a.txt")).unwrap(),
        "Amore\n"
    );
    assert_eq!(
        fs::metadata(res.join("work/out/prove"))
            .unwrap()
            .permissions()
            .mode()
            & 0o777,
        0o755
    );
    assert!(!res.join("junk").exists());
    assert!(o.diagnostics.outputs_complete);
}

#[test]
fn timeout_preserves_truncated_stdout_stderr() {
    gate!();
    let t = scratch_dir();
    let mut s = spec(
        "echo started; echo oops >&2; head -c 200000 /dev/zero | tr '\\0' x; sleep 60",
        &t.path().join("out"),
    );
    s.wall_timeout = Duration::from_secs(2);
    let o = run(&s);
    assert_eq!(o.exit, Exit::TimedOut);
    assert!(stdout(&o).starts_with("started\nxxxx"));
    assert_eq!(o.stdout_trunc.len(), 64 * 1024);
    assert_eq!(o.stdout_bytes, 8 + 200_000);
    assert_eq!(o.stderr_trunc, b"oops\n");
    assert!(
        (2_000_000_000..2_200_000_000).contains(&o.wall_ns),
        "wall {}",
        o.wall_ns
    );
}

#[test]
fn disk_io_is_rate_limited() {
    gate!();
    let work = deps().join("work-tests");
    let mut cfg = FirecrackerConfig::from_deps_dir(&deps(), &work).unwrap();
    cfg.drive_rate_limit = Some(arena_fc_proto::DriveRateLimit {
        bytes_per_s: 16 << 20,
        ops_per_s: 100_000,
        burst_bytes: 0,
    });
    let slow = FirecrackerSandbox::new(cfg).unwrap();
    let t = scratch_dir();
    let script = "dd if=/dev/zero of=/scratch/f bs=1M count=48 oflag=direct 2>/dev/null; echo done";
    let mut s = spec(script, &t.path().join("a"));
    s.rw_scratch_mb = 128;
    let fast = run(&s);
    let mut s2 = s.clone();
    s2.out_dir = t.path().join("b");
    let limited = slow.run_native(&s2).unwrap();
    assert_eq!(stdout(&fast), "done\n");
    assert_eq!(stdout(&limited), "done\n");
    // 48 MiB at 16 MiB/s >= ~2.8 s (the first bucket is full at start)
    assert!(
        limited.wall_ns > 2_500_000_000,
        "limited {}",
        limited.wall_ns
    );
    assert!(fast.wall_ns < 1_500_000_000, "default {}", fast.wall_ns);
    eprintln!(
        "48 MiB O_DIRECT write: default {:.0} ms, 16 MiB/s limit {:.0} ms",
        fast.wall_ns as f64 / 1e6,
        limited.wall_ns as f64 / 1e6
    );
}

/// A minimal root image (host dash + its libraries) replaces the arena
/// rootfs as the candidate's root.
#[test]
fn candidate_root_image() {
    gate!();
    let t = scratch_dir();
    let img = t.path().join("img");
    let ldd = std::process::Command::new("ldd")
        .arg("/usr/bin/dash")
        .output()
        .unwrap();
    let mut files = vec![PathBuf::from("/usr/bin/dash")];
    for l in String::from_utf8_lossy(&ldd.stdout).lines() {
        if let Some(p) = l.split_whitespace().find(|w| w.starts_with('/')) {
            files.push(PathBuf::from(p));
        }
    }
    for f in &files {
        let dst = img.join(f.strip_prefix("/").unwrap());
        fs::create_dir_all(dst.parent().unwrap()).unwrap();
        fs::copy(f, &dst).unwrap(); // follows symlinks
    }
    let lim = arena_archive::Limits::default();
    let digest = arena_archive::tree_from_dir(&img, &lim).unwrap().digest();
    let mut s = spec(
        "cd / && echo * && test -e /etc/debian_version || echo no-debian; echo hi > /scratch/out/x",
        &t.path().join("out"),
    );
    s.argv[0] = "/usr/bin/dash".into();
    s.root_image = Some(RootImage {
        dir: img.clone(),
        digest: digest.clone(),
    });
    let o = run(&s);
    assert_eq!(o.exit, Exit::Exited(0), "{o:?}");
    assert_eq!(
        stdout(&o),
        "dev lib lib64 proc scratch sys tmp usr\nno-debian\n"
    );
    assert_eq!(o.outputs.len(), 1);
    // a wrong digest is refused
    let mut bad = s.clone();
    bad.out_dir = t.path().join("out2");
    bad.root_image = Some(RootImage {
        dir: img,
        digest: arena_types::Digest::of_bytes(b"x"),
    });
    assert!(matches!(
        sandbox().run_native(&bad),
        Err(InfraError::InvalidSpec(_))
    ));
}

#[test]
fn rw_dirs_seed_and_write_back_safely() {
    gate!();
    let t = scratch_dir();
    let host = t.path().join("rw");
    fs::create_dir_all(host.join("sub")).unwrap();
    fs::write(host.join("keep.txt"), "seed").unwrap();
    fs::write(host.join("sub/edit.txt"), "old").unwrap();
    // judge-planted link, resolved inside the guest only
    std::os::unix::fs::symlink("/in/ro/data.txt", host.join("link.txt")).unwrap();
    let ro = t.path().join("ro");
    fs::create_dir_all(&ro).unwrap();
    fs::write(ro.join("data.txt"), "via-link").unwrap();
    let mut s = spec(
        "cd /arena/rw && cat keep.txt link.txt && echo new > sub/edit.txt && echo hi > made.txt && \
         ln -s /etc/passwd evil && echo x > link.txt 2>/dev/null || echo ro-target",
        &t.path().join("out"),
    );
    s.ro_mounts = vec![RoMount {
        host_path: ro,
        guest_path: "/in/ro".into(),
    }];
    s.rw_dirs = vec![RwDir {
        host_dir: host.clone(),
        guest_path: "/arena/rw".into(),
    }];
    s.allow_mount_symlinks = false;
    let o = run(&s);
    assert_eq!(o.exit, Exit::Exited(0), "{o:?}");
    assert_eq!(stdout(&o), "seedvia-linkro-target\n");
    assert_eq!(
        fs::read_to_string(host.join("sub/edit.txt")).unwrap(),
        "new\n"
    );
    assert_eq!(fs::read_to_string(host.join("made.txt")).unwrap(), "hi\n");
    assert_eq!(fs::read_to_string(host.join("keep.txt")).unwrap(), "seed");
    // the host link is untouched and the guest-made symlink never came back
    assert_eq!(
        fs::read_link(host.join("link.txt")).unwrap(),
        PathBuf::from("/in/ro/data.txt")
    );
    assert!(fs::symlink_metadata(host.join("evil")).is_err());
    assert!(o.outputs.iter().all(|(p, _)| !p.starts_with(".rw")));
}

/// Steps mode (one VM for a batch of invocations): per-step timing, inputs
/// visible only to their own step, outputs per step, and no state carried
/// from one step to the next (scratch, /tmp, /dev/shm, SysV IPC, processes).
#[test]
fn steps_share_one_vm_but_no_state() {
    gate!();
    use arena_sandbox::{Mount, Sandbox, SandboxSpec, StepSpec};
    let dir = scratch_dir();
    let inputs: Vec<PathBuf> = (0..3)
        .map(|i| {
            let p = dir.path().join(format!("req{i}.bin"));
            fs::write(&p, format!("request-{i}")).unwrap();
            p
        })
        .collect();
    let script = r#"
set -u
mkdir -p out
# what did earlier steps leave behind?
leak=""
for p in /scratch/marker /tmp/marker /dev/shm/marker; do [ -e "$p" ] && leak="$leak $p"; done
if command -v ipcs >/dev/null && ipcs -m | grep -q 0x0000abcd; then leak="$leak sysv-shm"; fi
for p in /proc/[0-9]*; do [ "$p" = "/proc/$$" ] && continue; cat "$p/comm" 2>/dev/null; done | grep -q '^sleep$' && leak="$leak process"
[ "$(ls /in | tr '\n' ,)" = "request.bin," ] || leak="$leak inputs:$(ls /in | tr '\n' ,)"
printf '%s|%s' "$(cat /in/request.bin)" "$leak" > out/result.txt
# now try to leave state for the next step
echo x > /scratch/marker; echo x > /tmp/marker; echo x > /dev/shm/marker 2>/dev/null
command -v ipcmk >/dev/null && ipcmk -M 4096 -p 0666 >/dev/null 2>&1 || true
(sleep 1000 &) 2>/dev/null
exit 0
"#;
    let mut base = SandboxSpec::new(vec!["/bin/sh".into(), "-c".into(), script.into()]);
    base.cwd = "/scratch".into();
    base.wall_timeout = Duration::from_secs(20);
    let steps: Vec<StepSpec> = inputs
        .iter()
        .enumerate()
        .map(|(i, p)| StepSpec {
            argv: base.argv.clone(),
            ro_files: vec![Mount {
                host: p.clone(),
                guest: "/in/request.bin".into(),
            }],
            collect: vec!["out".into()],
            out_dir: Some(dir.path().join(format!("out{i}"))),
            wall_timeout: Duration::from_secs(20),
        })
        .collect();
    assert!(sandbox().steps_share_instance());
    let outs = sandbox().run_steps(&base, &steps).expect("steps run");
    assert_eq!(outs.len(), 3);
    for (i, o) in outs.iter().enumerate() {
        assert_eq!(
            o.exit,
            Exit::Exited(0),
            "step {i}: {:?} {}",
            o.exit,
            String::from_utf8_lossy(&o.stderr_trunc)
        );
        assert!(o.output_error.is_none(), "{:?}", o.output_error);
        assert!(o.wall_ns > 0 && o.entry_wall_ns.is_some());
        // the host-clock step time brackets the guest's own measurement
        let g = o.entry_wall_ns.unwrap();
        assert!(
            o.wall_ns + 5_000_000 >= g,
            "host {} < guest {}",
            o.wall_ns,
            g
        );
        let r = fs::read_to_string(dir.path().join(format!("out{i}/out/result.txt"))).unwrap();
        assert_eq!(
            r,
            format!("request-{i}|"),
            "step {i} saw leaked state or a wrong input: {r:?}"
        );
        assert_eq!(o.outputs.len(), 1);
        assert_eq!(o.outputs[0].0, "out/result.txt");
    }
    // a failing step stops the batch
    let mut bad = steps.clone();
    for (i, s) in bad.iter_mut().enumerate() {
        s.out_dir = Some(dir.path().join(format!("bad{i}")));
    }
    bad[1].argv = vec!["/bin/sh".into(), "-c".into(), "exit 7".into()];
    let outs = sandbox().run_steps(&base, &bad).expect("steps run");
    assert_eq!(outs.len(), 2);
    assert_eq!(outs[1].exit, Exit::Exited(7));
}

#[test]
fn seccomp_violations_are_contained_and_reported() {
    gate!();
    let t = scratch_dir();
    // ptrace(PTRACE_TRACEME), unshare(CLONE_NEWUSER), socket(AF_INET), mount:
    // each must fail (EPERM) and be reported; the program keeps running
    let script = "perl -e 'print syscall(101, 0, 0, 0, 0), \"\\n\"' ; \
                  perl -e 'print syscall(272, 0x10000000), \"\\n\"' ; \
                  perl -MSocket -e 'socket(my $s, PF_INET, SOCK_STREAM, 0) ? print \"open\\n\" : print \"denied\\n\"' ; \
                  perl -MSocket -e 'socket(my $s, PF_UNIX, SOCK_STREAM, 0) ? print \"unix ok\\n\" : print \"unix denied\\n\"' ; \
                  echo done";
    let o = run(&spec(script, &t.path().join("out")));
    assert_eq!(o.exit, Exit::Exited(0), "{o:?}");
    assert_eq!(stdout(&o), "-1\n-1\ndenied\nunix ok\ndone\n");
    let mut v = o.violations.clone();
    v.sort();
    assert_eq!(
        v,
        vec!["ptrace x1", "socket(AF_INET) x1", "unshare x1"],
        "{v:?}"
    );

    // Tooling policy: sockets are not violations (builds judged by effect)
    let mut s = spec("perl -MSocket -e 'socket(my $s, PF_INET, SOCK_STREAM, 0)'; perl -e 'syscall(165, 0, 0, 0, 0, 0)'; true", &t.path().join("o2"));
    s.syscall_policy = arena_seccomp::Policy::Tooling;
    let o = run(&s);
    assert_eq!(o.violations, vec!["mount x1"]);

    // honest workloads are clean (threads, forks, pipes, files, /proc)
    let o = run(&spec(
        "for i in 1 2 3; do (head -c 1000000 /dev/urandom | sha256sum >/dev/null) & done; wait; \
         perl -e 'use threads; $_->join for map { threads->create(sub { 1 }) } 1..4' 2>/dev/null; \
         ls /proc/self/fd >/dev/null; cat /proc/cpuinfo >/dev/null; nproc; echo ok",
        &t.path().join("o3"),
    ));
    assert!(o.violations.is_empty(), "{:?}", o.violations);
    assert!(stdout(&o).ends_with("ok\n"));
}
