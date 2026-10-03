//! Conformance + adversarial + benchmark through the production Firecracker
//! backend; the toy build runs through bwrap-dev, and a second test builds a
//! Rust+C package through Firecracker with the pinned toolchain image.
//! Gated: `ARENA_FC_TESTS=1` (and `ARENA_DEV_UNSAFE=1` for the build).

mod common;

use arena_jobs::*;
use arena_types::{GateStatus, ReasonCode};
use common::*;
use arena_worker::executor::BuildEnv;
use std::sync::Arc;

#[test]
fn honest_candidate_through_firecracker() {
    if std::env::var("ARENA_FC_TESTS").as_deref() != Ok("1") {
        eprintln!("skipped: set ARENA_FC_TESTS=1");
        return;
    }
    let f = fixture();
    let (b, built) = f.build(&package_files());
    let (pkg, manifest, out) = built.unwrap_or_else(|| panic!("{:?}", b.gates));
    let deps = std::env::var_os("ARENA_FC_DEPS").map(std::path::PathBuf::from).unwrap_or_else(|| "/data/illia/nearproof-deps/firecracker".into());
    let cfg = arena_firecracker::FirecrackerConfig::from_deps_dir(&deps, &deps.join("work-worker-tests")).unwrap();
    let fc = arena_firecracker::FirecrackerSandbox::new(cfg).unwrap();
    let exec = common::executor(Arc::new(fc), f.store.clone(), &f.tmp.path().join("fc-jobs"));
    assert_eq!(exec.tier_cap(), arena_types::challenge::Tier::Formal);
    let run = |spec| arena_worker::executor::JobExecutor::execute(&exec, &spec, "fc", &std::sync::atomic::AtomicBool::new(false)).unwrap();
    let job = f.exec_job(&pkg, &manifest, &out);
    for spec in [JobSpec::Conformance(job.clone()), JobSpec::Adversarial(job.clone()), JobSpec::Benchmark(job)] {
        let r = run(spec);
        assert_eq!(r.execution.sandbox_backend, "firecracker");
        for g in &r.gates {
            let ok = g.status == GateStatus::Pass || g.summary.contains("CACHING_SUSPECTED");
            assert!(ok, "{:?}: {:?} {}", g.gate, g.status, g.summary);
            assert!(!g.reason_codes.contains(&ReasonCode::DemoOnly), "firecracker results are not tier-capped");
        }
    }
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

    let f = fixture();
    let deps = std::env::var_os("ARENA_FC_DEPS").map(std::path::PathBuf::from).unwrap_or_else(|| "/data/illia/nearproof-deps/firecracker".into());
    let cfg = arena_firecracker::FirecrackerConfig::from_deps_dir(&deps, &deps.join("work-worker-tests")).unwrap();
    let fc = arena_firecracker::FirecrackerSandbox::new(cfg).unwrap();
    let mut exec = common::executor(Arc::new(fc), f.store.clone(), &f.tmp.path().join("fc-jobs"));
    exec.ctx.build = BuildEnv { mounts: vec![], path: None, env: vec![], images_dir: Some(images.clone()), toolchain_image: Some(tc.clone()) };

    // The toy C candidate plus a vendored-crate Rust tool, built offline.
    let mut files = package_files();
    let toy_build = String::from_utf8(files["build-recipe/build.sh"].1.clone()).unwrap();
    set(
        &mut files,
        "build-recipe/build.sh",
        &format!("{toy_build}(cd source/tool && cargo build -q --release --offline --locked --target-dir ../../target)\ncp target/release/tool out/tool\ncc -O2 -o out/ctool source/c/hello.c\n./out/tool > out/tool.txt\n./out/ctool >> out/tool.txt\n"),
    );
    let m = String::from_utf8(files["candidate.toml"].1.clone()).unwrap().replace("\"out/verify\"]", "\"out/verify\", \"out/tool.txt\"]");
    set(&mut files, "candidate.toml", &m);
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
    let (v, pkg) = f.validate(&files);
    assert_eq!(v.gates[0].status, GateStatus::Pass, "{}", v.gates[0].summary);
    let manifest = v.manifest.unwrap();
    let mut chal = f.chal.clone();
    chal.resource_limits.max_build_ms = 600_000;
    let run = |spec| arena_worker::executor::JobExecutor::execute(&exec, &spec, "fc-build", &std::sync::atomic::AtomicBool::new(false)).unwrap();
    let b = run(JobSpec::Build(BuildJob { ctx: f.ctx(&pkg), challenge: chal, manifest: manifest.clone() }));
    let g = &b.gates[0];
    assert_eq!(g.status, GateStatus::Pass, "{} // {:?}", g.summary, g.reason_codes);
    let out = b.build.unwrap();
    assert_eq!(out.toolchain_image.as_deref(), Some(tc.as_str()));

    // the built bundle runs in microVMs (arena runtime rootfs)
    let c = run(JobSpec::Conformance(f.exec_job(&pkg, &manifest, &out)));
    for g in &c.gates {
        assert_eq!(g.status, GateStatus::Pass, "{:?}: {}", g.gate, g.summary);
    }
}
