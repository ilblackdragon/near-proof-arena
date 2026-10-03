//! Lean inside Firecracker microVMs with the pinned lean-checker image
//! (`deploy/images/lean-checker/build.sh`).
//!
//! * `formal_checker_corpus_in_microvms`: runs runners/formal-checker's real
//!   pipeline (reference build, sandboxed elaboration, leanchecker, lean4lean,
//!   lean4export + nanoda, arena-audit) with every untrusted step in a fresh
//!   microVM, through `FirecrackerLeanRunner` below — an `UntrustedRunner`
//!   adapter over `FirecrackerSandbox` (read-write output dirs, stdout-to-file,
//!   tools served from the digest-pinned image). Cases: the positive toy and
//!   five negatives (override with `FC_CASES=a,b,...`).
//! * `native_lean_compiles_in_microvm`: `lean -c` + `leanc` (bundled clang +
//!   lld + glibc stubs) build and run a native executable inside a VM — the
//!   `verify_route = "native-lean"` judge build.
//!
//! Gated: `ARENA_FC_TESTS=1` and an installed image under
//! `$LEAN_CHECKER_IMAGES` (default /data/illia/nearproof-deps/lean-checker/images).

use arena_firecracker::*;
use arena_formal_checker::sandbox::{
    InfraError as FcInfra, RunExit, RunOutcome, RunSpec, CAPTURE_LIMIT,
};
use arena_formal_checker::*;
use arena_types::{Digest, GateStatus, ObligationId, ReasonCode};
use serde_json::Value;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

fn enabled() -> bool {
    std::env::var("ARENA_FC_TESTS").as_deref() == Ok("1")
}

fn deps() -> PathBuf {
    std::env::var_os("ARENA_FC_DEPS")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/data/illia/nearproof-deps/firecracker"))
}

/// (image dir, digest) of the newest installed lean-checker image.
fn lean_image() -> (PathBuf, Digest) {
    let dir = std::env::var_os("LEAN_CHECKER_IMAGES")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/data/illia/nearproof-deps/lean-checker/images"));
    let mut metas: Vec<(std::time::SystemTime, PathBuf)> = std::fs::read_dir(&dir)
        .expect("lean-checker images dir (run deploy/images/lean-checker/build.sh)")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .map(|p| (p.metadata().unwrap().modified().unwrap(), p))
        .collect();
    metas.sort();
    let meta: Value = serde_json::from_slice(
        &std::fs::read(&metas.last().expect("an image manifest").1).unwrap(),
    )
    .unwrap();
    let digest: Digest = meta["digest"]
        .as_str()
        .unwrap()
        .to_string()
        .try_into()
        .unwrap();
    (dir.join(digest.hex()), digest)
}

fn sandbox() -> FirecrackerSandbox {
    let cfg = FirecrackerConfig::from_deps_dir(&deps(), &deps().join("work-lean-tests")).unwrap();
    FirecrackerSandbox::new(cfg).unwrap()
}

/// `UntrustedRunner` over the Firecracker backend with the lean-checker image
/// as the candidate root.
struct FirecrackerLeanRunner {
    sb: FirecrackerSandbox,
    image: RootImage,
    work: PathBuf,
    n: AtomicU64,
    vm_runs: AtomicU64,
    vm_ns: AtomicU64,
}

const G_STDOUT: &str = "/arena/.stdout";

impl FirecrackerLeanRunner {
    /// Read-only mounts of files/dirs that are part of the pinned image are
    /// served by the image itself (same bytes, verified by digest) instead of
    /// being re-imaged for every run.
    fn provided_by_image(&self, host: &Path, guest: &Path) -> bool {
        let rel = guest.strip_prefix("/").unwrap_or(guest);
        host == self.image.dir.join(rel)
    }
}

impl UntrustedRunner for FirecrackerLeanRunner {
    fn id(&self) -> &str {
        "firecracker"
    }
    fn demo_only(&self) -> bool {
        false
    }
    fn run(&self, spec: &RunSpec, capture_limit: usize) -> Result<RunOutcome, FcInfra> {
        let k = self.n.fetch_add(1, Ordering::Relaxed);
        let run_dir = self.work.join(format!("run-{}-{k}", std::process::id()));
        std::fs::create_dir_all(&run_dir)?;
        // stdout goes to a file when it is a report (> 64 KiB cap) or the
        // caller streams it to a host file
        let to_file = spec.stdout_file.is_some() || capture_limit > CAPTURE_LIMIT;
        let mut argv = spec.argv.clone();
        let mut rw_dirs: Vec<RwDir> = spec
            .rw
            .iter()
            .map(|(h, g)| RwDir {
                host_dir: h.clone(),
                guest_path: g.display().to_string(),
            })
            .collect();
        let stdout_dir = run_dir.join("stdout");
        if to_file {
            std::fs::create_dir_all(&stdout_dir)?;
            let mut w = vec![
                "/bin/sh".into(),
                "-c".into(),
                format!("exec \"$0\" \"$@\" > {G_STDOUT}/out"),
            ];
            w.append(&mut argv);
            argv = w;
            rw_dirs.push(RwDir {
                host_dir: stdout_dir.clone(),
                guest_path: G_STDOUT.into(),
            });
        }
        let mut req = RunRequest::new(self.sb.rootfs_digest().clone(), argv, run_dir.join("out"));
        req.root_image = Some(self.image.clone());
        req.ro_mounts = spec
            .ro
            .iter()
            .filter(|(h, g)| !self.provided_by_image(h, g))
            .map(|(h, g)| RoMount {
                host_path: h.clone(),
                guest_path: g.display().to_string(),
            })
            .collect();
        req.rw_dirs = rw_dirs;
        req.allow_mount_symlinks = true; // judge-built olean link farms
        req.env = spec.env.clone();
        req.cwd = spec.cwd.display().to_string();
        req.wall_timeout = spec.wall_timeout;
        req.mem_bytes = spec.mem_bytes.unwrap_or(4 << 30).min(8 << 30);
        req.pids = 1024;
        req.cpu_set = vec![];
        req.rw_scratch_mb = (spec.max_file_bytes >> 20).clamp(256, 16 << 10);
        req.scratch_dirs = vec![];
        req.collect = vec![];
        let t = Instant::now();
        let res = self.sb.run_native(&req);
        self.vm_runs.fetch_add(1, Ordering::Relaxed);
        self.vm_ns
            .fetch_add(t.elapsed().as_nanos() as u64, Ordering::Relaxed);
        let o = res.map_err(|e| FcInfra::Io(std::io::Error::other(format!("firecracker: {e}"))))?;
        let mut stdout = o.stdout_trunc.clone();
        if to_file {
            let p = stdout_dir.join("out");
            match &spec.stdout_file {
                Some(dst) => {
                    std::fs::copy(&p, dst)?;
                }
                None => {
                    let mut b = std::fs::read(&p).unwrap_or_default();
                    b.truncate(capture_limit);
                    stdout = b;
                }
            }
        }
        let exit = match o.exit {
            Exit::Exited(c) => RunExit::Exited(c),
            Exit::Signaled(s) => RunExit::Signaled(s),
            Exit::TimedOut => RunExit::TimedOut,
            Exit::OomKilled => RunExit::Signaled(9),
            Exit::ExecFailed => RunExit::Exited(127),
        };
        let _ = std::fs::remove_dir_all(&run_dir);
        Ok(RunOutcome {
            exit,
            wall: Duration::from_nanos(o.wall_ns),
            stdout,
            stderr: o.stderr_trunc,
        })
    }
}

fn fc_crate() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../formal-checker")
}

fn names(rep: &FormalCheckReport) -> (Vec<String>, Vec<String>) {
    let s = |v: Value| v.as_str().unwrap().to_string();
    let mut st: Vec<String> = rep
        .gates
        .iter()
        .map(|g| s(serde_json::to_value(g.status).unwrap()))
        .collect();
    st.sort();
    st.dedup();
    let mut codes: Vec<String> = rep
        .gates
        .iter()
        .flat_map(|g| {
            g.reason_codes
                .iter()
                .map(|c| s(serde_json::to_value(c).unwrap()))
        })
        .collect();
    codes.sort();
    codes.dedup();
    (st, codes)
}

#[test]
fn formal_checker_corpus_in_microvms() {
    if !enabled() {
        eprintln!("skipped: set ARENA_FC_TESTS=1");
        return;
    }
    let (img_dir, digest) = lean_image();
    let tools = toolchain::ToolPaths {
        lean_sysroot: img_dir.join("arena/tc"),
        lean4export: img_dir.join("arena/tools/lean4export"),
        nanoda: Some(img_dir.join("arena/tools/nanoda_bin")),
        lean4lean: Some(img_dir.join("arena/tools/lean4lean")),
        arena_audit: img_dir.join("arena/tools/arena-audit"),
    };
    let work = deps()
        .join("work-lean-tests")
        .join(format!("corpus-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&work);
    std::fs::create_dir_all(&work).unwrap();
    let t_img = Instant::now();
    let runner = FirecrackerLeanRunner {
        sb: sandbox(),
        image: RootImage {
            dir: img_dir.clone(),
            digest: digest.clone(),
        },
        work: work.join("runner"),
        n: AtomicU64::new(0),
        vm_runs: AtomicU64::new(0),
        vm_ns: AtomicU64::new(0),
    };
    let runner = std::sync::Arc::new(runner);
    struct Shared(std::sync::Arc<FirecrackerLeanRunner>);
    impl UntrustedRunner for Shared {
        fn id(&self) -> &str {
            self.0.id()
        }
        fn demo_only(&self) -> bool {
            self.0.demo_only()
        }
        fn run(&self, s: &RunSpec, c: usize) -> Result<RunOutcome, FcInfra> {
            self.0.run(s, c)
        }
    }
    let checker = FormalChecker::new(tools, Box::new(Shared(runner.clone())));
    let expected: TemplateExpected = serde_json::from_slice(
        &std::fs::read(fc_crate().join("tests/fixtures/expected.json")).unwrap(),
    )
    .unwrap();
    let trusted = vec![TrustedPackage {
        name: "arena-standin".into(),
        src_root: fc_crate().join("tests/fixtures/standin"),
        include: None,
    }];
    let cases: Vec<String> = std::env::var("FC_CASES")
        .map(|s| s.split(',').map(str::to_string).collect())
        .unwrap_or_else(|_| {
            [
                "pos_basic",
                "neg_sorry",
                "neg_axiom_false",
                "neg_native_decide",
                "neg_wrong_type",
                "neg_eval_fake_pass",
            ]
            .map(String::from)
            .to_vec()
        });
    let mut failures = Vec::new();
    let mut first = true;
    for name in &cases {
        let case = fc_crate().join("tests/corpus").join(name);
        let expect: Value =
            serde_json::from_slice(&std::fs::read(case.join("expect.json")).unwrap()).unwrap();
        let mut policy = Policy {
            allowed_requires: vec!["arena-standin".into()],
            ..Policy::default()
        };
        if expect.get("conjuncts").and_then(Value::as_bool) == Some(true) {
            policy.conjunct_gates = Some(vec![
                ObligationId::FormalSemanticSoundness,
                ObligationId::FormalSemanticCompleteness,
                ObligationId::FormalCryptoSoundness,
                ObligationId::FormalImplConnection,
            ]);
        }
        let scratch = work.join(name);
        let req = CheckRequest {
            formal_dir: case.join("formal"),
            certificate: "Candidate.certificate".into(),
            trusted: trusted.clone(),
            expected: &expected,
            challenge_digest: None,
            policy,
            limits: {
                let mut l = Limits::default();
                if let Some(t) = expect.get("module_timeout_s").and_then(Value::as_u64) {
                    l.module_timeout = Duration::from_secs(t);
                }
                l
            },
            work_dir: scratch.join("work"),
            cache_dir: work.join("ref-cache"),
        };
        let runs0 = runner.vm_runs.load(Ordering::Relaxed);
        let t = Instant::now();
        let rep = checker.check(&req);
        let wall = t.elapsed();
        let runs = runner.vm_runs.load(Ordering::Relaxed) - runs0;
        let (st, codes) = names(&rep);
        let rc: Vec<String> = rep
            .rechecks
            .iter()
            .filter(|r| r.ran)
            .map(|r| format!("{}={}", r.id, r.verdict))
            .collect();
        eprintln!(
            "{name:<22} {:>6.1}s {runs:>3} VMs  {:<8} {:<50} {}{}",
            wall.as_secs_f64(),
            st.join("/"),
            codes.join(","),
            rc.join(" "),
            if first {
                "  (incl. first-use image staging + reference build)"
            } else {
                ""
            }
        );
        first = false;
        // expectations, same semantics as runners/formal-checker/tests/corpus.rs
        if let Some(all) = expect.get("all") {
            let want = all["status"].as_str().unwrap();
            if st != vec![want.to_string()] {
                failures.push(format!("{name}: statuses {st:?}, expected {want}"));
            }
            for c in all["codes"].as_array().unwrap() {
                if !codes.iter().any(|x| Some(x.as_str()) == c.as_str()) {
                    failures.push(format!("{name}: missing code {c} (got {codes:?})"));
                }
            }
        }
        if let Some(per) = expect.get("gates").and_then(Value::as_object) {
            for (g, e) in per {
                let gate = rep
                    .gates
                    .iter()
                    .find(|x| serde_json::to_value(x.gate).unwrap().as_str() == Some(g.as_str()));
                let Some(gate) = gate else {
                    failures.push(format!("{name}: gate {g} missing"));
                    continue;
                };
                if serde_json::to_value(gate.status).unwrap().as_str() != e["status"].as_str() {
                    failures.push(format!(
                        "{name}: gate {g} is {:?}, expected {}",
                        gate.status, e["status"]
                    ));
                }
            }
        }
        if expect.get("check_no_fake_pass").and_then(Value::as_bool) == Some(true)
            && rep.gates.iter().any(|g| g.status == GateStatus::Pass)
        {
            failures.push(format!("{name}: fake PASS influenced a gate"));
        }
        if name.starts_with("pos_") {
            assert!(
                rep.gates.iter().all(|g| g.status == GateStatus::Pass),
                "{name}: {:?}",
                rep.findings
            );
            let ran: Vec<&str> = rep
                .rechecks
                .iter()
                .filter(|r| r.ran)
                .map(|r| r.id.as_str())
                .collect();
            for want in ["leanchecker", "nanoda"] {
                assert!(
                    ran.iter().any(|r| r.contains(want)),
                    "{name}: recheckers ran {ran:?}"
                );
            }
        }
        if rep
            .gates
            .iter()
            .any(|g| g.reason_codes.contains(&ReasonCode::InfraError))
        {
            failures.push(format!("{name}: infra error: {:?}", rep.findings));
        }
    }
    let n = runner.vm_runs.load(Ordering::Relaxed).max(1);
    eprintln!(
        "image {digest}: {} microVM runs, mean {:.2}s per run, total {:.1}s",
        n,
        runner.vm_ns.load(Ordering::Relaxed) as f64 / n as f64 / 1e9,
        t_img.elapsed().as_secs_f64()
    );
    let _ = std::fs::remove_dir_all(&work);
    assert!(failures.is_empty(), "failures:\n{}", failures.join("\n"));
}

#[test]
fn native_lean_compiles_in_microvm() {
    if !enabled() {
        eprintln!("skipped: set ARENA_FC_TESTS=1");
        return;
    }
    let (img_dir, digest) = lean_image();
    let sb = sandbox();
    let work = deps()
        .join("work-lean-tests")
        .join(format!("native-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&work);
    let src = work.join("src");
    std::fs::create_dir_all(&src).unwrap();
    std::fs::write(
        src.join("Verifier.lean"),
        "def check (xs : List Nat) : Bool := xs.foldl (· + ·) 0 == 42\n\
         def main (args : List String) : IO UInt32 := do\n\
         \x20 let ok := check (args.map String.toNat!)\n\
         \x20 IO.println s!\"accept={ok}\"\n\
         \x20 return if ok then 0 else 1\n",
    )
    .unwrap();
    let script = "set -e; cd /scratch; \
        lean -R /in/src -c Verifier.c /in/src/Verifier.lean; \
        leanc -O2 -o verifier Verifier.c; \
        ./verifier 40 2; ./verifier 1 2 || echo rejected=$?; \
        cp verifier out/verifier";
    let mut req = RunRequest::new(
        sb.rootfs_digest().clone(),
        vec!["/bin/sh".into(), "-c".into(), script.into()],
        work.join("out"),
    );
    req.root_image = Some(RootImage {
        dir: img_dir,
        digest,
    });
    req.ro_mounts = vec![RoMount {
        host_path: src,
        guest_path: "/in/src".into(),
    }];
    req.env = vec![("PATH".into(), "/arena/tc/bin:/usr/bin:/bin".into())];
    req.mem_bytes = 2 << 30;
    req.rw_scratch_mb = 1024;
    req.wall_timeout = Duration::from_secs(300);
    let t = Instant::now();
    let o = sb.run_native(&req).unwrap();
    eprintln!(
        "native-lean build+run in VM: {:.2}s total, {:.2}s in guest; stderr: {}",
        t.elapsed().as_secs_f64(),
        o.wall_ns as f64 / 1e9,
        String::from_utf8_lossy(&o.stderr_trunc)
    );
    assert_eq!(
        o.exit,
        Exit::Exited(0),
        "{}",
        String::from_utf8_lossy(&o.stderr_trunc)
    );
    assert_eq!(
        String::from_utf8_lossy(&o.stdout_trunc),
        "accept=true\naccept=false\nrejected=1\n"
    );
    assert_eq!(o.outputs.len(), 1);
    let _ = std::fs::remove_dir_all(&work);
}
