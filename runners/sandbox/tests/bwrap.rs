//! Integration tests for the bwrap-dev backend. Require `ARENA_DEV_UNSAFE=1`,
//! bubblewrap, and unprivileged user namespaces. Each isolation property is
//! checked in both limit-enforcement modes where it matters (delegated
//! cgroup v2 if available, and the rlimit fallback).

use arena_sandbox::*;
use std::path::PathBuf;
use std::process::Command;
use std::time::{Duration, Instant};

fn dev_unsafe() {
    assert_eq!(
        std::env::var("ARENA_DEV_UNSAFE").as_deref(),
        Ok("1"),
        "bwrap-dev tests must run with ARENA_DEV_UNSAFE=1"
    );
}

struct Env {
    sb: BwrapDev,
    tmp: tempfile::TempDir,
}

fn env_with(mode: CgroupMode) -> Env {
    dev_unsafe();
    let tmp = tempfile::tempdir().unwrap();
    let mut cfg = BwrapConfig::new(HelperCommand::new(env!("CARGO_BIN_EXE_arena-sandbox-helper")), tmp.path().join("work"));
    cfg.cgroup = mode;
    Env { sb: BwrapDev::new(cfg).unwrap(), tmp }
}

fn env() -> Env {
    env_with(CgroupMode::Auto)
}

fn sh(script: &str) -> SandboxSpec {
    let mut s = SandboxSpec::new(vec!["/bin/sh".into(), "-c".into(), script.into()]);
    s.wall_timeout = Duration::from_secs(20);
    s
}

fn out(o: &SandboxOutcome) -> String {
    String::from_utf8_lossy(&o.stdout_trunc).into_owned()
}

fn err(o: &SandboxOutcome) -> String {
    String::from_utf8_lossy(&o.stderr_trunc).into_owned()
}

fn host_has_process(marker: &str) -> bool {
    let o = Command::new("pgrep").args(["-f", marker]).output().unwrap();
    !o.stdout.is_empty()
}

#[test]
fn runs_and_stamps_demo_isolation() {
    let e = env();
    let o = e.sb.run(&sh("echo hello; echo oops >&2")).unwrap();
    assert_eq!(o.exit, ExitStatus::Exited(0), "{}", err(&o));
    assert_eq!(out(&o), "hello\n");
    assert_eq!(err(&o), "oops\n");
    assert_eq!(o.isolation, "bwrap-dev (DEMO-only)");
    assert_eq!(o.tier_cap, Some(arena_types::challenge::Tier::Demo));
    assert_eq!(e.sb.tier_cap(), Some(arena_types::challenge::Tier::Demo));
    assert!(o.wall_ns > 0 && o.entry_wall_ns.unwrap() <= o.wall_ns);
    if e.sb.uses_cgroup() {
        assert_eq!(o.limits, LimitEnforcement::CgroupV2);
        assert!(o.peak_rss_bytes > 0);
    }
}

#[test]
fn exit_codes_signals_exec_failure() {
    let e = env();
    assert_eq!(e.sb.run(&sh("exit 3")).unwrap().exit, ExitStatus::Exited(3));
    assert_eq!(e.sb.run(&sh("kill -SEGV $$")).unwrap().exit, ExitStatus::Signaled(11));
    let o = e.sb.run(&SandboxSpec::new(vec!["/nonexistent/prove".into()])).unwrap();
    assert_eq!(o.exit, ExitStatus::ExecFailed);
}

#[test]
fn network_is_denied() {
    let e = env();
    let o = e
        .sb
        .run(&sh(
            "cat /proc/net/dev | tail -n +3 | cut -d: -f1 | tr -d ' '; \
             for t in 1.1.1.1/53 127.0.0.1/55471 8.8.8.8/443; do \
               if timeout 3 bash -c \"echo > /dev/tcp/$t\" 2>/dev/null; then echo CONNECTED $t; fi; done; \
             if python3 -c 'import socket; socket.getaddrinfo(\"example.com\", 80)' 2>/dev/null; then echo DNS; fi",
        ))
        .unwrap();
    assert_eq!(o.exit, ExitStatus::Exited(0), "{}", err(&o));
    assert_eq!(out(&o), "lo\n", "only loopback, no connections, no DNS: {}", out(&o));
}

#[test]
fn host_filesystem_is_hidden() {
    let e = env();
    let home = std::env::var("HOME").unwrap();
    let probe = e.tmp.path().join("secret");
    std::fs::write(&probe, "s3cret").unwrap();
    let script = format!(
        "for p in {home} /home /data /root /etc/passwd /etc/shadow /run /var {probe} /sys/fs/cgroup; do \
           if [ -e \"$p\" ]; then echo VISIBLE $p; fi; done; \
         cat {probe} 2>/dev/null; ls / | tr '\\n' ' '",
        probe = probe.display()
    );
    let o = e.sb.run(&sh(&script)).unwrap();
    assert_eq!(o.exit, ExitStatus::Exited(0), "{}", err(&o));
    let s = out(&o);
    assert!(!s.contains("VISIBLE") && !s.contains("s3cret"), "{s}");
}

#[test]
fn writes_confined_to_scratch() {
    let e = env();
    let ro = e.tmp.path().join("ro");
    std::fs::create_dir(&ro).unwrap();
    std::fs::write(ro.join("f"), "x").unwrap();
    let mut s = sh(
        "for p in /x /usr/x /etc/x /in/ro/x /in/ro/f /.arena/x /proc/x /dev/x; do \
           if (echo hi > $p) 2>/dev/null; then echo WROTE $p; fi; done; \
         echo ok > /scratch/a && echo ok > /tmp/b && cat /scratch/a /scratch/tmp/b; cat /in/ro/f",
    );
    s.ro_mounts.push(Mount { host: ro.clone(), guest: "/in/ro".into() });
    let o = e.sb.run(&s).unwrap();
    assert_eq!(o.exit, ExitStatus::Exited(0), "{}", err(&o));
    assert_eq!(out(&o), "ok\nok\nx");
    assert_eq!(std::fs::read_dir(&ro).unwrap().count(), 1);
}

#[test]
fn scratch_is_size_limited() {
    let e = env();
    let mut s = sh("head -c 8000000 /dev/zero > /scratch/big; echo rc=$?; head -c 32000000 /dev/zero > /dev/shm/x; echo shm=$?");
    s.rw_scratch_mb = 4;
    let o = e.sb.run(&s).unwrap();
    assert!(out(&o).contains("rc=1"), "{} {}", out(&o), err(&o));
    assert!(out(&o).contains("shm=1"), "{} {}", out(&o), err(&o));
}

#[test]
fn no_leaked_env_vars() {
    // A canary in the supervisor's own environment must not reach the sandbox.
    std::env::set_var("ARENA_TEST_CANARY", "leak");
    let e = env();
    let o = e.sb.run(&SandboxSpec::new(vec!["/usr/bin/env".into()])).unwrap();
    let mut keys: Vec<String> = out(&o).lines().map(|l| l.split('=').next().unwrap().to_string()).collect();
    keys.sort();
    assert_eq!(keys, ["HOME", "LANG", "PATH", "PWD", "TMPDIR", "TZ"], "{}", out(&o));
    let mut s = SandboxSpec::new(vec!["/usr/bin/env".into()]);
    s.env.push(("SOURCE_DATE_EPOCH".into(), "0".into()));
    let o = e.sb.run(&s).unwrap();
    assert!(out(&o).contains("SOURCE_DATE_EPOCH=0"));
    s.env.push(("DATABASE_URL".into(), "postgres://x".into()));
    assert!(matches!(e.sb.run(&s), Err(InfraError::InvalidSpec(_))));
    let mut s = SandboxSpec::new(vec!["/usr/bin/env".into()]);
    s.env.push(("LD_PRELOAD".into(), "/x.so".into()));
    assert!(matches!(e.sb.run(&s), Err(InfraError::InvalidSpec(_))));
}

fn fork_bomb(mode: CgroupMode) {
    let e = env_with(mode);
    let marker = format!("arena-forkbomb-{}", std::process::id());
    let mut s = SandboxSpec::new(vec![
        "/bin/bash".into(),
        "-c".into(),
        format!("b() {{ b | b & }}; b; exec -a {marker} sleep 30"),
    ]);
    s.pids = 32;
    s.wall_timeout = Duration::from_secs(4);
    let t = Instant::now();
    let o = e.sb.run(&s).unwrap();
    assert!(t.elapsed() < Duration::from_secs(20));
    assert!(matches!(o.exit, ExitStatus::TimedOut | ExitStatus::Exited(_) | ExitStatus::Signaled(_)), "{:?}", o.exit);
    if e.sb.uses_cgroup() {
        assert!(o.pids_limit_hit, "pids.max should have been hit");
    }
    std::thread::sleep(Duration::from_millis(200));
    assert!(!host_has_process(&marker));
}

#[test]
fn fork_bomb_contained() {
    fork_bomb(CgroupMode::Auto);
}

#[test]
fn fork_bomb_contained_rlimit_fallback() {
    fork_bomb(CgroupMode::Off);
}

fn mem_hog(mode: CgroupMode) -> SandboxOutcome {
    let e = env_with(mode);
    let mut s = SandboxSpec::new(vec![
        "/usr/bin/python3".into(),
        "-c".into(),
        "b = bytearray(400 << 20)\nfor i in range(0, len(b), 4096): b[i] = 1\nprint('survived')".into(),
    ]);
    s.mem_bytes = 128 << 20;
    s.wall_timeout = Duration::from_secs(30);
    let o = e.sb.run(&s).unwrap();
    assert!(!out(&o).contains("survived"));
    o
}

#[test]
fn memory_limit_oom_detected() {
    let e = env();
    if !e.sb.uses_cgroup() {
        panic!("delegated cgroup v2 is unavailable on this host; OOM detection needs it (set ARENA_SANDBOX_CGROUP=off to skip knowingly)");
    }
    let o = mem_hog(CgroupMode::Auto);
    assert_eq!(o.exit, ExitStatus::OomKilled);
    assert!(o.peak_rss_bytes <= 129 << 20, "peak {}", o.peak_rss_bytes);
}

#[test]
fn memory_limit_rlimit_fallback() {
    let o = mem_hog(CgroupMode::Off);
    assert_eq!(o.limits, LimitEnforcement::Rlimit);
    assert_ne!(o.exit, ExitStatus::Exited(0));
}

#[test]
fn timeout_kills_grandchildren() {
    let e = env();
    let marker = format!("arena-grandchild-{}", std::process::id());
    let mut s = sh(&format!(
        "(setsid bash -c 'exec -a {marker} sleep 1000' &); (bash -c 'exec -a {marker}-b sleep 1000' &); sleep 1000"
    ));
    s.wall_timeout = Duration::from_secs(1);
    let t = Instant::now();
    let o = e.sb.run(&s).unwrap();
    assert_eq!(o.exit, ExitStatus::TimedOut);
    assert!(o.wall_ns >= 1_000_000_000 && t.elapsed() < Duration::from_secs(10));
    std::thread::sleep(Duration::from_millis(200));
    assert!(!host_has_process(&marker));
}

#[test]
fn background_processes_do_not_outlive_entry() {
    let e = env();
    let marker = format!("arena-daemon-{}", std::process::id());
    let o = e.sb.run(&sh(&format!("(setsid bash -c 'exec -a {marker} sleep 1000' &); echo started"))).unwrap();
    assert_eq!(o.exit, ExitStatus::Exited(0));
    std::thread::sleep(Duration::from_millis(200));
    assert!(!host_has_process(&marker));
}

#[test]
fn outputs_collected_and_digested() {
    let e = env();
    let dest = e.tmp.path().join("out");
    let mut s = sh("mkdir -p o/sub && printf claim > o/claim.bin && printf proof > o/sub/p && chmod +x o/sub/p && printf x > ignored");
    s.collect = vec!["o".into(), "missing".into()];
    s.out_dir = Some(dest.clone());
    let o = e.sb.run(&s).unwrap();
    assert_eq!(o.exit, ExitStatus::Exited(0), "{}", err(&o));
    assert_eq!(o.output_error, None);
    let names: Vec<&str> = o.outputs.iter().map(|(p, _)| p.as_str()).collect();
    assert_eq!(names, ["o/claim.bin", "o/sub/p"]);
    assert_eq!(o.outputs[0].1, arena_types::Digest::of_bytes(b"claim"));
    assert_eq!(std::fs::read(dest.join("o/sub/p")).unwrap(), b"proof");
    assert!(!dest.join("ignored").exists());
    let t = arena_archive::tree_from_dir(&dest, &arena_archive::Limits::default()).unwrap();
    assert_eq!(Some(t.digest()), o.outputs_tree);
    assert!(t.is_exec("o/sub/p"));
}

#[test]
fn hostile_outputs_rejected() {
    let e = env();
    for (script, needle) in [
        ("mkdir o; ln -s /etc/passwd o/l", "not a regular file"),
        ("mkdir o; mkfifo o/f", "not a regular file"),
        ("mkdir o; head -c 3000000 /dev/zero > o/big", "expanded size"),
    ] {
        let dest = e.tmp.path().join(format!("out-{}", needle.len()));
        let _ = std::fs::remove_dir_all(&dest);
        let mut s = sh(script);
        s.collect = vec!["o".into()];
        s.out_dir = Some(dest.clone());
        s.max_output_bytes = 1 << 20;
        let o = e.sb.run(&s).unwrap();
        let msg = o.output_error.clone().unwrap_or_default();
        assert!(msg.contains(needle), "{script}: {msg:?}");
        assert!(o.outputs.is_empty());
        assert_eq!(std::fs::read_dir(&dest).unwrap().count(), 0);
    }
}

#[test]
fn stdout_truncated() {
    let e = env();
    let o = e.sb.run(&sh("head -c 1000000 /dev/zero | tr '\\0' a")).unwrap();
    assert_eq!(o.stdout_trunc.len(), 64 * 1024);
    assert_eq!(o.stdout_bytes, 1_000_000);
}

#[test]
fn copy_in_gives_writable_copy() {
    let e = env();
    let pkg = e.tmp.path().join("pkg");
    std::fs::create_dir_all(pkg.join("d")).unwrap();
    std::fs::write(pkg.join("d/f"), "data\n").unwrap();
    let mut s = sh("test -d made/x || exit 9; cd work && cat d/f && echo more >> d/f && cat d/f | wc -l");
    s.ro_mounts.push(Mount { host: pkg.clone(), guest: "/in/pkg".into() });
    s.copy_in.push(CopyIn { from_guest: "/in/pkg".into(), to_scratch: "work".into() });
    s.scratch_dirs.push("made/x".into());
    let o = e.sb.run(&s).unwrap();
    assert_eq!(out(&o), "data\n2\n", "{}", err(&o));
    assert_eq!(std::fs::read(pkg.join("d/f")).unwrap(), b"data\n");
}

#[test]
fn measures_wall_and_cpu() {
    let e = env();
    let o = e.sb.run(&sh("sleep 0.3")).unwrap();
    assert!(o.wall_ns >= 300_000_000, "{}", o.wall_ns);
    let o = e.sb.run(&sh("i=0; while [ $i -lt 300000 ]; do i=$((i+1)); done")).unwrap();
    assert!(o.cpu_ns >= 50_000_000, "cpu {}", o.cpu_ns);
}

#[test]
fn spec_validation() {
    let e = env();
    let mut s = sh("true");
    s.ro_mounts.push(Mount { host: PathBuf::from("/usr"), guest: "/usr".into() });
    assert!(matches!(e.sb.run(&s), Err(InfraError::InvalidSpec(_))));
    let mut s = sh("true");
    s.ro_mounts.push(Mount { host: PathBuf::from("/usr"), guest: "/in/../etc".into() });
    assert!(matches!(e.sb.run(&s), Err(InfraError::InvalidSpec(_))));
    let mut s = sh("true");
    s.collect.push("../x".into());
    s.out_dir = Some(e.tmp.path().join("o"));
    assert!(matches!(e.sb.run(&s), Err(InfraError::InvalidSpec(_))));
}

#[test]
fn cannot_tamper_with_init() {
    let e = env();
    // PID 1 is the judge's init: non-dumpable and immune to in-namespace kills.
    let o = e
        .sb
        .run(&sh("kill -9 1 2>/dev/null; cat /proc/1/environ >/dev/null 2>&1 && echo READ_ENV; \
                  head -c 1 /proc/1/mem >/dev/null 2>&1 && echo READ_MEM; echo alive"))
        .unwrap();
    assert_eq!(o.exit, ExitStatus::Exited(0), "{}", err(&o));
    assert_eq!(out(&o), "alive\n");
}
