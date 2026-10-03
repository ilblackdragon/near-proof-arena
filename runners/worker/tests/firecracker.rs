//! Conformance + adversarial + benchmark through the production Firecracker
//! backend (build through bwrap-dev: firecracker has no copy-in yet).
//! Gated: `ARENA_FC_TESTS=1` (and `ARENA_DEV_UNSAFE=1` for the build).

mod common;

use arena_jobs::*;
use arena_types::{GateStatus, ReasonCode};
use common::*;
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
