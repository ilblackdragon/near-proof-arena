//! Conformance + adversarial + benchmark through the production Firecracker
//! backend (build through bwrap-dev: firecracker has no copy-in yet).
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
    let c = run(JobSpec::Conformance(ConformanceJob { bundle: bundle.clone(), entry: entry(), params: f.put(b"params-v1"), cases: cases.clone(), limits: run_limits() }));
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
    };
    let r = run(JobSpec::Benchmark(bj));
    let g = r.gates.iter().find(|g| g.gate == ObligationId::Benchmark).unwrap();
    assert_eq!(g.status, GateStatus::Pass, "{}", g.summary);
    let res = r.benchmark.unwrap();
    assert!(!res.measured_by.contains("DEMO"));
    assert!(res.classes[0].median_ns > 0 && res.score_milli.is_some());

    let bad = run(JobSpec::Conformance(ConformanceJob { bundle, entry: entry(), params: f.put(b"params-v1"), cases: f.cases(1, true, |_| b"nope".to_vec()), limits: run_limits() }));
    let g = bad.gates.iter().find(|g| g.gate == ObligationId::ConformanceDifferential).unwrap();
    assert!(g.reason_codes.contains(&ReasonCode::ClaimMismatch), "{}", g.summary);
}
