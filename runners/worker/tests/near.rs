//! The formal NEAR challenge end to end through the worker stages with the
//! reference candidate `examples/reexec-witness` (native-lean route): build
//! (Rust + Lean toolchains mounted read-only), FORMAL_CHECK against the real
//! NEAR statement, conformance / adversarial on the NEAR oracle with the
//! judge-built native verifier, benchmark. bwrap-dev (job tier overridden to
//! demo; the pipeline is identical). Opt-in: `ARENA_NEAR_TESTS=1` plus the
//! host toolchains and a built `near-arena-oracle`.

mod common;

use arena_jobs::*;
use arena_sandbox::Mount;
use arena_types::{ChallengeDefinition, GateStatus, ObligationId, VerifiedSurface};
use arena_worker::executor::{BuildEnv, FormalEnv, JobExecutor};
use arena_worker::oracle::Oracles;
use common::*;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;

const NEAR: &str = "chl_5ef2bc7d2068219635426e47ca46bfbb";

fn git_files(rel: &str) -> std::collections::BTreeMap<String, (u32, Vec<u8>)> {
    let out = std::process::Command::new("git").arg("-C").arg(repo()).args(["ls-files", "-s", "--", rel]).output().unwrap();
    let mut m = std::collections::BTreeMap::new();
    for l in String::from_utf8(out.stdout).unwrap().lines() {
        let (meta, path) = l.split_once('\t').unwrap();
        let mode = if meta.starts_with("100755") { 0o755 } else { 0o644 };
        m.insert(path.strip_prefix(&format!("{rel}/")).unwrap().to_string(), (mode, std::fs::read(repo().join(path)).unwrap()));
    }
    m
}

fn export(rel: &str, dest: &Path) {
    for (p, (_, b)) in git_files(rel) {
        let d = dest.join(rel).join(p);
        std::fs::create_dir_all(d.parent().unwrap()).unwrap();
        std::fs::write(d, b).unwrap();
    }
}

pub fn near_env(f: &mut Fixture) -> Option<()> {
    let oracle = std::env::var_os("ARENA_NEAR_ORACLE").map(PathBuf::from).unwrap_or_else(|| repo().join("oracle/target/debug/near-arena-oracle"));
    if !oracle.is_file() {
        eprintln!("SKIP: no near-arena-oracle at {}", oracle.display());
        return None;
    }
    let home = PathBuf::from(std::env::var("HOME").unwrap());
    let rust = home.join(".rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu");
    let lean = home.join(".elan/toolchains/leanprover--lean4---v4.34.1");
    f.exec.ctx.build = BuildEnv {
        mounts: vec![Mount { host: rust, guest: "/opt/rust".into() }, Mount { host: lean, guest: "/opt/lean".into() }],
        path: Some("/opt/rust/bin:/opt/lean/bin:/usr/bin:/bin".into()),
        env: vec![],
        images_dir: None,
        toolchain_image: None,
    };
    let mut o = Oracles::builtin().with_near(oracle, &repo().join("spec/workloads/near-transfer-receipt-v1")).unwrap();
    let clean = f.tmp.path().join("clean");
    export("oracle/fixtures/public", &clean);
    let fx = o.add_fixtures_dir(&clean.join("oracle/fixtures/public")).unwrap();
    assert_eq!(fx.as_str(), "sha256:c83f3e14d526e78244ee2d7288396a9680717fa42ef77127ba29ccf27bb7e6ec");
    f.exec.ctx.oracles = o;
    export("formal-core", &clean);
    export("spec/lean", &clean);
    f.exec.ctx.formal = Some(FormalEnv { repo: clean, configs_dir: repo().join("runners/formal-checker/challenges"), images_dir: None });
    f.exec.ctx.bench_batch_cap = Some(1);
    f.exec.ctx.conformance_samples = 3;
    f.chal = serde_json::from_slice::<ChallengeDefinition>(&std::fs::read(repo().join(format!("challenges/{NEAR}.json"))).unwrap()).unwrap();
    // Test-only re-pin: the signed challenge pins the identity of one build
    // of the host checker tools; this host's tools may have been rebuilt.
    f.chal.toolchain_policy.checker_image = arena_formal_checker::toolchain::ToolPaths::discover().unwrap().image_digest().unwrap();
    Some(())
}

fn ctx(f: &Fixture, pkg: &arena_types::Digest) -> JobContext {
    let mut c = f.ctx(pkg);
    c.challenge_id = NEAR.into();
    c.challenge_digest = f.chal.digest().unwrap();
    c.tier = arena_types::challenge::Tier::Demo;
    c
}

fn run(f: &Fixture, spec: JobSpec) -> JobResult {
    let t = std::time::Instant::now();
    let kind = spec.kind();
    let r = f.exec.execute(&spec, "near", &AtomicBool::new(false)).unwrap();
    eprintln!("{kind}: {:?}", t.elapsed());
    for g in &r.gates {
        eprintln!("  {:?} {:?} {:?} {}", g.gate, g.status, g.reason_codes, &g.summary[..g.summary.len().min(160)]);
    }
    r
}

#[test]
fn reexec_witness_reference_all_stages() {
    if std::env::var("ARENA_NEAR_TESTS").as_deref() != Ok("1") {
        eprintln!("skipped: set ARENA_NEAR_TESTS=1");
        return;
    }
    let mut f = fixture();
    if near_env(&mut f).is_none() {
        return;
    }
    let pkg = f.put(&tar_of(&git_files("examples/reexec-witness")));
    let v = run(&f, JobSpec::Validate(ValidateJob { ctx: ctx(&f, &pkg), challenge: f.chal.clone() }));
    assert_eq!(v.gates[0].status, GateStatus::Pass);
    let manifest = v.manifest.unwrap();
    let b = run(&f, JobSpec::Build(BuildJob { ctx: ctx(&f, &pkg), challenge: f.chal.clone(), manifest: manifest.clone() }));
    assert_eq!(b.gates[0].status, GateStatus::Pass);
    let mut build = b.build.unwrap();
    let vs = VerifiedSurface {
        challenge_id: NEAR.into(),
        verify_artifact: build.verify.clone(),
        prepare_artifact: build.prepare.clone(),
        public_artifacts: build.public_artifacts.clone(),
        formal_tree: build.formal_tree.clone(),
        certificate_decl: build.certificate_decl.clone(),
        checker_image: f.chal.toolchain_policy.checker_image.clone(),
    };
    let fc = run(&f, JobSpec::FormalCheck(FormalCheckJob { ctx: ctx(&f, &pkg), challenge: f.chal.clone(), manifest: manifest.clone(), build: build.clone(), verified_surface: vs }));
    for g in &fc.gates {
        if g.gate != ObligationId::FormalZk {
            assert_eq!(g.status, GateStatus::Pass, "{:?}: {}", g.gate, g.summary);
        }
    }
    build.native_verifier = Some(fc.native_verifier.clone().expect("judge-built native verifier"));
    let job = ExecJob { ctx: ctx(&f, &pkg), challenge: f.chal.clone(), manifest, build };
    let c = run(&f, JobSpec::Conformance(job.clone()));
    for g in &c.gates {
        assert_eq!(g.status, GateStatus::Pass, "{:?}: {}", g.gate, g.summary);
    }
    let a = run(&f, JobSpec::Adversarial(job.clone()));
    assert_eq!(a.gates[0].status, GateStatus::Pass, "{}", a.gates[0].summary);
    let r = run(&f, JobSpec::Benchmark(job));
    assert_eq!(r.gates[0].status, GateStatus::Pass, "{}", r.gates[0].summary);
}

/// The same flow with production isolation: every stage in Firecracker
/// microVMs (build in the pinned Rust toolchain image with the Lean
/// toolchain from the lean-checker image mounted read-only; FORMAL_CHECK on
/// the lean-checker image). The challenge copy is re-pinned to that image's
/// checker identity (test-only). Gated: `ARENA_NEAR_TESTS=1 ARENA_FC_TESTS=1`.
#[test]
fn reexec_witness_reference_firecracker() {
    if std::env::var("ARENA_NEAR_TESTS").as_deref() != Ok("1") || std::env::var("ARENA_FC_TESTS").as_deref() != Ok("1") {
        eprintln!("skipped: set ARENA_NEAR_TESTS=1 ARENA_FC_TESTS=1");
        return;
    }
    let mut f = fixture();
    if near_env(&mut f).is_none() {
        return;
    }
    let deps = std::env::var_os("ARENA_FC_DEPS").map(PathBuf::from).unwrap_or_else(|| "/data/illia/nearproof-deps/firecracker".into());
    let tc_images: PathBuf = "/data/illia/nearproof-deps/toolchain-images".into();
    let lean_images: PathBuf = "/data/illia/nearproof-deps/lean-checker/images".into();
    let pick = |dir: &Path| -> (PathBuf, arena_types::Digest) {
        let mut metas: Vec<_> = std::fs::read_dir(dir)
            .unwrap()
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|x| x == "json"))
            .map(|p| (p.metadata().unwrap().modified().unwrap(), p))
            .collect();
        metas.sort();
        let meta = metas.pop().unwrap().1;
        let v: serde_json::Value = serde_json::from_slice(&std::fs::read(meta).unwrap()).unwrap();
        let d: arena_types::Digest = v["digest"].as_str().unwrap().to_string().try_into().unwrap();
        (dir.join(d.hex()), d)
    };
    let (_, tc) = pick(&tc_images);
    let (lean_img, _) = pick(&lean_images);
    let cfg = arena_firecracker::FirecrackerConfig::from_deps_dir(&deps, &deps.join("work-worker-tests")).unwrap();
    let fc = arena_firecracker::FirecrackerSandbox::new(cfg).unwrap();
    let bw_exec = std::mem::replace(&mut f.exec, common::executor(std::sync::Arc::new(fc), f.store.clone(), &f.tmp.path().join("fc-near")));
    f.exec.ctx.oracles = bw_exec.ctx.oracles;
    f.exec.ctx.formal = bw_exec.ctx.formal.map(|mut e| {
        e.images_dir = Some(lean_images.clone());
        e
    });
    f.exec.ctx.bench_batch_cap = Some(1);
    f.exec.ctx.conformance_samples = 3;
    f.exec.ctx.build = BuildEnv {
        mounts: vec![Mount { host: lean_img.join("arena/tc"), guest: "/opt/lean".into() }],
        path: Some("/opt/lean/bin:/usr/local/rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin:/usr/local/cargo/bin:/usr/local/bin:/usr/bin:/bin".into()),
        env: vec![],
        images_dir: Some(tc_images.clone()),
        toolchain_image: Some(tc),
    };
    let tools = arena_formal_checker::toolchain::ToolPaths {
        lean_sysroot: lean_img.join("arena/tc"),
        lean4export: lean_img.join("arena/tools/lean4export"),
        nanoda: Some(lean_img.join("arena/tools/nanoda_bin")),
        lean4lean: Some(lean_img.join("arena/tools/lean4lean")),
        arena_audit: lean_img.join("arena/tools/arena-audit"),
    };
    f.chal.toolchain_policy.checker_image = tools.image_digest().unwrap();
    let pkg = f.put(&tar_of(&git_files("examples/reexec-witness")));
    let mut c = ctx(&f, &pkg);
    c.tier = arena_types::challenge::Tier::Formal;
    let v = run(&f, JobSpec::Validate(ValidateJob { ctx: c.clone(), challenge: f.chal.clone() }));
    let manifest = v.manifest.unwrap();
    let b = run(&f, JobSpec::Build(BuildJob { ctx: c.clone(), challenge: f.chal.clone(), manifest: manifest.clone() }));
    assert_eq!(b.gates[0].status, GateStatus::Pass);
    let mut build = b.build.unwrap();
    let vs = VerifiedSurface {
        challenge_id: NEAR.into(),
        verify_artifact: build.verify.clone(),
        prepare_artifact: build.prepare.clone(),
        public_artifacts: build.public_artifacts.clone(),
        formal_tree: build.formal_tree.clone(),
        certificate_decl: build.certificate_decl.clone(),
        checker_image: f.chal.toolchain_policy.checker_image.clone(),
    };
    let fcr = run(&f, JobSpec::FormalCheck(FormalCheckJob { ctx: c.clone(), challenge: f.chal.clone(), manifest: manifest.clone(), build: build.clone(), verified_surface: vs }));
    for g in &fcr.gates {
        assert_eq!(g.status, GateStatus::Pass, "{:?}: {}", g.gate, g.summary);
    }
    build.native_verifier = Some(fcr.native_verifier.clone().expect("judge-built native verifier"));
    let job = ExecJob { ctx: c, challenge: f.chal.clone(), manifest, build };
    for spec in [JobSpec::Conformance(job.clone()), JobSpec::Adversarial(job.clone()), JobSpec::Benchmark(job)] {
        let r = run(&f, spec);
        for g in &r.gates {
            assert_eq!(g.status, GateStatus::Pass, "{:?}: {}", g.gate, g.summary);
        }
    }
}
