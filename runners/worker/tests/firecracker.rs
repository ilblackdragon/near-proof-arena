//! Conformance + adversarial + benchmark through the production Firecracker
//! backend; the toy build runs through bwrap-dev, and a second test builds a
//! Rust+C package through Firecracker with the pinned toolchain image.
//! Gated: `ARENA_FC_TESTS=1` (and `ARENA_DEV_UNSAFE=1` for the build).

mod common;

use arena_types::{GateStatus, ObligationId, ReasonCode};
use arena_worker::executor::{BuildEnv, JobExecutor, StageExecutor, WorkerContext};
use arena_worker::jobs::*;
use arena_worker::mutators::MutatorRegistry;
use common::*;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

#[test]
fn honest_candidate_through_firecracker() {
    if std::env::var("ARENA_FC_TESTS").as_deref() != Ok("1") {
        eprintln!("skipped: set ARENA_FC_TESTS=1");
        return;
    }
    let f = fixture();
    let (b, bundle) = f.build(&package_files());
    assert_eq!(b.gates[0].status, GateStatus::Pass, "{}", b.gates[0].summary);
    let bundle = bundle.unwrap();

    let deps = std::env::var_os("ARENA_FC_DEPS").map(std::path::PathBuf::from).unwrap_or_else(|| "/data/illia/nearproof-deps/firecracker".into());
    let fc_work = deps.join("work-worker-tests");
    let cfg = arena_firecracker::FirecrackerConfig::from_deps_dir(&deps, &fc_work).unwrap();
    let fc = arena_firecracker::FirecrackerSandbox::new(cfg).unwrap();
    let exec = StageExecutor::new(WorkerContext {
        worker_id: "fc-test".into(),
        sandbox: Arc::new(fc),
        store: f.store.clone(),
        work_root: f.tmp.path().join("fc-jobs"),
        build: BuildEnv::default(),
        bench_cpus: None,
        mutators: MutatorRegistry::generic(),
        keep_workdirs: false,
    });
    assert_eq!(exec.sandbox_info().tier_cap, None);
    let run = |spec| exec.execute(&job("fc", spec), &AtomicBool::new(false)).unwrap();

    let cases = f.cases(2, true, claim_for);
    let c = run(JobSpec::Conformance(ConformanceJob { bundle: bundle.clone(), entry: entry(), params: f.put(b"params-v1"), cases: cases.clone(), limits: run_limits(), request_pin: None }));
    for g in &c.gates {
        assert_eq!(g.status, GateStatus::Pass, "{:?}: {} // all: {:?}", g.gate, g.summary, c.gates.iter().map(|g| (&g.gate, &g.reason_codes, &g.summary)).collect::<Vec<_>>());
        assert!(!g.reason_codes.contains(&ReasonCode::DemoOnly), "firecracker results are not tier-capped");
    }
    // Same bundle + params ⇒ same public dir digest as under bwrap-dev.
    let honest: Vec<HonestProof> = cases
        .iter()
        .map(|k| HonestProof {
            case_id: k.id.clone(),
            claim: c.artifact(&format!("claim:{}", k.id)).unwrap().clone(),
            proof: c.artifact(&format!("proof:{}", k.id)).unwrap().clone(),
        })
        .collect();
    let a = run(JobSpec::Adversarial(AdversarialJob {
        bundle: bundle.clone(),
        entry: entry(),
        public_artifacts: c.artifact("public_artifacts").unwrap().clone(),
        honest,
        mutators: vec!["truncate".into(), "swap".into(), "append".into()],
        seed: 3,
        limits: run_limits(),
    }));
    let g = a.gates.iter().find(|g| g.gate == ObligationId::AdversarialProofs).unwrap();
    assert_eq!(g.status, GateStatus::Pass, "{}", g.summary);

    let bj = BenchmarkJob {
        bundle: bundle.clone(),
        entry: entry(),
        params: f.put(b"params-v1"),
        public_artifacts: None,
        classes: vec![BenchClass { class_id: "c".into(), weight_ppm: 1_000_000, baseline_ns: 1_000_000_000, batch: f.cases(1, true, claim_for), fresh_batch: vec![] }],
        procedure: arena_types::challenge::MeasurementProcedure {
            warmup_runs: 1,
            measured_runs: 3,
            aggregation: "median".into(),
            outlier_mad_k: 1000,
            cold_runs: 1,
            concurrency: 1,
            per_run_timeout_ms: 20_000,
        },
        hardware_profile: "dev-host".into(),
        suite_revision: "r1".into(),
        schedule_seed: 1,
        bootstrap_seed: 2,
        bootstrap_iterations: 100,
        limits: run_limits(),
        request_pin: None,
    };
    let r = run(JobSpec::Benchmark(bj));
    let g = r.gates.iter().find(|g| g.gate == ObligationId::Benchmark).unwrap();
    assert_eq!(g.status, GateStatus::Pass, "{}", g.summary);
    let res = r.benchmark.unwrap();
    assert!(!res.measured_by.contains("DEMO"));
    assert!(res.classes[0].median_ns > 0 && res.score_milli.is_some());

    let bad = run(JobSpec::Conformance(ConformanceJob { bundle, entry: entry(), params: f.put(b"params-v1"), cases: f.cases(1, true, |_| b"nope".to_vec()), limits: run_limits(), request_pin: None }));
    let g = bad.gates.iter().find(|g| g.gate == ObligationId::ConformanceDifferential).unwrap();
    assert!(g.reason_codes.contains(&ReasonCode::ClaimMismatch), "{}", g.summary);
}

/// BUILD_REPRODUCIBLE through Firecracker with the pinned Rust/cc toolchain
/// image (`deploy/images/toolchain/build.sh`): the package is copied into
/// scratch, a vendored-crate Rust binary and a C binary are built offline
/// twice and must be bit-identical; the bundle then passes conformance in
/// microVMs. Gated: `ARENA_FC_TESTS=1` and an installed toolchain image
/// (`ARENA_TOOLCHAIN_IMAGES`, default /data/illia/nearproof-deps/toolchain-images).
#[test]
fn build_through_firecracker_with_pinned_toolchain() {
    if std::env::var("ARENA_FC_TESTS").as_deref() != Ok("1") {
        eprintln!("skipped: set ARENA_FC_TESTS=1");
        return;
    }
    let images = std::env::var_os("ARENA_TOOLCHAIN_IMAGES")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| "/data/illia/nearproof-deps/toolchain-images".into());
    let meta_path = std::fs::read_dir(&images)
        .expect("toolchain images dir (run deploy/images/toolchain/build.sh)")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .find(|p| p.extension().is_some_and(|x| x == "json"))
        .expect("a toolchain image manifest");
    let meta: serde_json::Value = serde_json::from_slice(&std::fs::read(&meta_path).unwrap()).unwrap();
    let tc: arena_types::Digest = meta["digest"].as_str().unwrap().to_string().try_into().unwrap();
    let env = meta["env"].as_object().unwrap();

    let f = fixture();
    let deps = std::env::var_os("ARENA_FC_DEPS").map(std::path::PathBuf::from).unwrap_or_else(|| "/data/illia/nearproof-deps/firecracker".into());
    let cfg = arena_firecracker::FirecrackerConfig::from_deps_dir(&deps, &deps.join("work-worker-tests")).unwrap();
    let fc = arena_firecracker::FirecrackerSandbox::new(cfg).unwrap();
    let exec = StageExecutor::new(WorkerContext {
        worker_id: "fc-build-test".into(),
        sandbox: Arc::new(fc),
        store: f.store.clone(),
        work_root: f.tmp.path().join("fc-jobs"),
        build: BuildEnv {
            mounts: vec![],
            path: Some(env["PATH"].as_str().unwrap().into()),
            env: vec![("CARGO_HOME".into(), env["CARGO_HOME"].as_str().unwrap().into())],
            images_dir: Some(images.clone()),
        },
        bench_cpus: None,
        mutators: MutatorRegistry::generic(),
        keep_workdirs: false,
    });

    let mut files = package_files();
    files.insert(
        "build-recipe/build.sh".into(),
        (0o755, br#"#!/bin/sh
set -e
mkdir -p out
for f in prepare prove verify; do cp source/$f.sh out/$f; chmod 755 out/$f; done
(cd source/tool && cargo build -q --release --offline --locked --target-dir ../../target)
cp target/release/tool out/tool
cc -O2 -o out/ctool source/c/hello.c
./out/tool > out/tool.txt
./out/ctool >> out/tool.txt
"#.to_vec()),
    );
    let tinydep_toml = b"[package]\nname = \"tinydep\"\nversion = \"0.1.0\"\nedition = \"2021\"\n".to_vec();
    let tinydep_lib = b"pub fn answer() -> u32 { 42 }\n".to_vec();
    let sha = |b: &[u8]| arena_types::Digest::of_bytes(b).hex().to_string();
    let checksum = format!(
        "{{\"files\":{{\"Cargo.toml\":\"{}\",\"src/lib.rs\":\"{}\"}},\"package\":\"6f7b844a2cb058abc9b4e34e7d851609617c0c3c02ad851b81e8c6421aad6414\"}}",
        sha(&tinydep_toml),
        sha(&tinydep_lib)
    );
    for (p, b) in [
        ("source/tool/Cargo.toml", b"[package]\nname = \"tool\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[dependencies]\ntinydep = \"0.1\"\n".to_vec()),
        ("source/tool/Cargo.lock", b"# This file is automatically @generated by Cargo.\n# It is not intended for manual editing.\nversion = 4\n\n[[package]]\nname = \"tinydep\"\nversion = \"0.1.0\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\nchecksum = \"6f7b844a2cb058abc9b4e34e7d851609617c0c3c02ad851b81e8c6421aad6414\"\n\n[[package]]\nname = \"tool\"\nversion = \"0.1.0\"\ndependencies = [\n \"tinydep\",\n]\n".to_vec()),
        ("source/tool/src/main.rs", b"fn main() { println!(\"tool says {}\", tinydep::answer()); }\n".to_vec()),
        ("source/tool/.cargo/config.toml", b"[source.crates-io]\nreplace-with = \"vendored-sources\"\n\n[source.vendored-sources]\ndirectory = \"vendor\"\n".to_vec()),
        ("source/tool/vendor/tinydep/Cargo.toml", tinydep_toml.clone()),
        ("source/tool/vendor/tinydep/src/lib.rs", tinydep_lib.clone()),
        ("source/tool/vendor/tinydep/.cargo-checksum.json", checksum.into_bytes()),
        ("source/c/hello.c", b"#include <stdio.h>\nint main(void) { puts(\"c says hi\"); return 0; }\n".to_vec()),
    ] {
        files.insert(p.into(), (0o644, b));
    }
    let pkg = f.put(&tar_of(&files));
    let mut limits = build_limits();
    limits.max_build_ms = 600_000;
    limits.mem_bytes = 2 << 30;
    limits.pids = 512;
    limits.scratch_mb = 2048;
    limits.max_output_bytes = 64 << 20;
    let b = exec
        .execute(
            &job("fc-build", JobSpec::Build(BuildJob { package: pkg, toolchain_image: Some(tc.clone()), limits, source_date_epoch: 0 })),
            &AtomicBool::new(false),
        )
        .unwrap();
    let g = &b.gates[0];
    assert_eq!(g.status, GateStatus::Pass, "{} // {:?}", g.summary, g.reason_codes);
    assert_eq!(b.artifact("toolchain_image"), Some(&tc));
    let bundle = b.artifact("bundle").unwrap().clone();

    // the built bundle runs in microVMs (arena runtime rootfs)
    let cases = f.cases(1, true, claim_for);
    let c = exec.execute(
        &job("fc-conf", JobSpec::Conformance(ConformanceJob { bundle, entry: entry(), params: f.put(b"params-v1"), cases, limits: run_limits(), request_pin: None })),
        &AtomicBool::new(false),
    ).unwrap();
    for g in &c.gates {
        assert_eq!(g.status, GateStatus::Pass, "{:?}: {}", g.gate, g.summary);
    }
}
