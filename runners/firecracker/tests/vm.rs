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

fn spec(script: &str, out: &Path) -> SandboxSpec {
    SandboxSpec {
        rootfs_digest: sandbox().rootfs_digest().clone(),
        ro_mounts: vec![],
        rw_scratch_mb: 64,
        argv: vec!["/bin/sh".into(), "-c".into(), script.into()],
        env: vec![],
        cpu_set: vec![],
        mem_bytes: 256 << 20,
        pids: 64,
        wall_timeout: Duration::from_secs(20),
        network: None,
        out_dir: out.to_path_buf(),
    }
}

fn run(s: &SandboxSpec) -> SandboxOutcome {
    let o = sandbox().run(s).expect("sandbox run");
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
    let o = run(&spec("echo hello; echo oops >&2; id -u; pwd", &t.path().join("out")));
    assert_eq!(o.exit, Exit::Exited(0), "{o:?}");
    assert_eq!(stdout(&o), "hello\n1000\n/arena/scratch\n");
    assert_eq!(o.stderr_trunc, b"oops\n");
    assert!(o.diagnostics.boot_ns.is_some());
    assert!(o.cpu_ns > 0 && o.peak_rss_bytes > 0);
}

#[test]
fn exit_codes_and_signals() {
    gate!();
    let t = scratch_dir();
    assert_eq!(run(&spec("exit 3", &t.path().join("a"))).exit, Exit::Exited(3));
    assert_eq!(run(&spec("exit 1", &t.path().join("b"))).exit, Exit::Exited(1));
    assert_eq!(run(&spec("kill -SEGV $$", &t.path().join("c"))).exit, Exit::Signaled(11));
    let mut s = spec("", &t.path().join("d"));
    s.argv = vec!["/nonexistent/prove".into()];
    let o = run(&s);
    assert_eq!(o.exit, Exit::Exited(127));
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
    assert!(o.wall_ns >= 2_000_000_000 && o.wall_ns < 2_200_000_000, "wall {}", o.wall_ns);
    assert!(elapsed < Duration::from_secs(10), "host elapsed {elapsed:?}");
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
        let mut s = spec(&format!("exec perl -e '{prog}'"), &t.path().join(format!("out{i}")));
        s.mem_bytes = 128 << 20;
        let o = run(&s);
        assert_eq!(o.exit, Exit::OomKilled, "{o:?}");
        assert_eq!(o.diagnostics.host_oom_kills, 0, "the guest limit, not the host one, must fire");
    }
    // the same program fits with a larger limit
    let mut s2 = spec(r#"exec perl -e '$x = "a" x (40*1024*1024); print length($x), "\n"'"#, &t.path().join("out2"));
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
             touch /etc/x 2>/dev/null && echo ROOT_WRITABLE; touch /arena/x 2>/dev/null && echo ARENA_WRITABLE; \
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
        "HOME=/arena/scratch\nPATH=/usr/local/bin:/usr/bin:/bin\nPWD=/arena/scratch\nRUST_LOG=info\nTMPDIR=/arena/scratch/tmp\n"
    );
    let mut bad = spec("true", &t.path().join("out2"));
    bad.env = vec![("LD_PRELOAD".into(), "/x.so".into())];
    assert!(matches!(sandbox().run(&bad), Err(InfraError::InvalidSpec(_))));
}

#[test]
fn outputs_retrieved_with_digests_and_policy() {
    gate!();
    let t = scratch_dir();
    let out = t.path().join("out");
    let o = run(&spec(
        "cd out && mkdir -p sub/deeper && printf 'claim' > claim.bin && head -c 300000 /dev/urandom > sub/proof.bin && \
         printf '#!/bin/sh\\necho hi\\n' > sub/deeper/tool && chmod +x sub/deeper/tool && ln -s /etc/passwd link && \
         mkfifo fifo && echo ok",
        &out,
    ));
    assert_eq!(o.exit, Exit::Exited(0), "{o:?}");
    let paths: Vec<&str> = o.outputs.iter().map(|(p, _)| p.as_str()).collect();
    assert_eq!(paths, vec!["claim.bin", "sub/deeper/tool", "sub/proof.bin"]); // sorted
    for (p, d) in &o.outputs {
        let bytes = fs::read(out.join(p)).unwrap();
        assert_eq!(d.hex(), hex::encode(Sha256::digest(&bytes)), "{p}");
    }
    assert_eq!(fs::read(out.join("claim.bin")).unwrap(), b"claim");
    assert_eq!(fs::metadata(out.join("sub/proof.bin")).unwrap().len(), 300000);
    assert_eq!(fs::metadata(out.join("sub/deeper/tool")).unwrap().permissions().mode() & 0o777, 0o755);
    assert!(!out.join("link").exists() && fs::symlink_metadata(out.join("link")).is_err());
    assert!(!o.diagnostics.outputs_complete);
    assert_eq!(o.diagnostics.output_violations.len(), 2, "{:?}", o.diagnostics.output_violations);
}

#[test]
fn ro_bundle_mounts() {
    gate!();
    let t = scratch_dir();
    let bundle = t.path().join("bundle");
    fs::create_dir_all(bundle.join("out")).unwrap();
    fs::write(bundle.join("out/prove"), "#!/bin/sh\necho \"proving $1\"\nexit 0\n").unwrap();
    fs::set_permissions(bundle.join("out/prove"), fs::Permissions::from_mode(0o755)).unwrap();
    fs::write(bundle.join("data.txt"), "params").unwrap();
    let req = t.path().join("request.bin");
    fs::write(&req, b"REQ").unwrap();
    let mut s = spec(
        "/arena/bundle/out/prove x && cat /arena/bundle/data.txt && echo && cat /arena/in/request.bin && echo && \
         (touch /arena/bundle/new 2>/dev/null && echo WRITABLE || echo ro) && \
         (echo y > /arena/in/request.bin 2>/dev/null && echo WRITABLE || echo ro)",
        &t.path().join("out"),
    );
    s.ro_mounts = vec![
        RoMount { host_path: bundle.clone(), guest_path: "/arena/bundle".into() },
        RoMount { host_path: req, guest_path: "/arena/in/request.bin".into() },
    ];
    let o = run(&s);
    assert_eq!(o.exit, Exit::Exited(0), "{o:?}");
    assert_eq!(stdout(&o), "proving x\nparams\nREQ\nro\nro\n");
    // symlinks in a bundle are refused before anything boots
    std::os::unix::fs::symlink("/etc/passwd", bundle.join("evil")).unwrap();
    assert!(matches!(sandbox().run(&s), Err(InfraError::InvalidSpec(_))));
}

#[test]
fn no_state_across_runs() {
    gate!();
    let t = scratch_dir();
    let o1 = run(&spec("echo a > /arena/scratch/persist; echo b > /tmp/persist; echo c > /dev/shm/persist; echo ok", &t.path().join("o1")));
    assert_eq!(stdout(&o1), "ok\n");
    let o2 = run(&spec("ls -A /arena/scratch /tmp /dev/shm", &t.path().join("o2")));
    assert_eq!(stdout(&o2), "/arena/scratch:\nout\ntmp\n\n/dev/shm:\n\n/tmp:\n");
}

#[test]
fn pids_limit_bounds_fork_bombs() {
    gate!();
    let t = scratch_dir();
    let mut s = spec("i=0; while [ $i -lt 200 ]; do sleep 5 & i=$((i+1)); done 2>/dev/null; echo spawned", &t.path().join("out"));
    s.pids = 16;
    s.wall_timeout = Duration::from_secs(15);
    let o = run(&s);
    // the shell survives fork failures; background sleeps are killed at exit
    assert!(matches!(o.exit, Exit::Exited(_)), "{o:?}");
    assert!(o.wall_ns < 5_000_000_000, "children must not outlive the candidate: {}", o.wall_ns);
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
        assert!((o.wall_ns as i64 - g as i64).abs() < 50_000_000, "host {} guest {g}", o.wall_ns);
    }
    for w in walls {
        assert!((1_000_000_000..1_150_000_000).contains(&w), "sleep 1 measured {w}ns");
    }
    // multi-vCPU pinned run: 2 busy loops on 2 vCPUs take ~1s wall, ~2s cpu
    let mut s = spec("for i in 1 2; do (end=$(($(date +%s)+1)); while [ $(date +%s) -lt $end ]; do :; done) & done; wait; nproc", &t.path().join("mc"));
    s.cpu_set = vec![2, 3];
    let o = run(&s);
    assert_eq!(stdout(&o), "2\n");
}
