//! Harness tests with a scripted sandbox: timings come only from the
//! supervisor's `wall_ns`; candidate output claiming timings is ignored.

use arena_measure::stats::Phase;
use arena_measure::*;
use arena_sandbox::*;
use arena_types::challenge::MeasurementProcedure;
use std::sync::Mutex;

struct Scripted {
    walls: Mutex<Vec<u64>>,
    calls: Mutex<Vec<String>>,
}

impl Sandbox for Scripted {
    fn name(&self) -> &str {
        "scripted"
    }
    fn tier_cap(&self) -> Option<arena_types::challenge::Tier> {
        None
    }
    fn run(&self, spec: &SandboxSpec) -> Result<SandboxOutcome, InfraError> {
        self.calls.lock().unwrap().push(spec.argv.join(" "));
        let wall = self.walls.lock().unwrap().remove(0);
        Ok(SandboxOutcome {
            exit: if wall == 0 {
                ExitStatus::TimedOut
            } else {
                ExitStatus::Exited(0)
            },
            wall_ns: wall,
            cpu_ns: wall,
            peak_rss_bytes: 1 << 20,
            max_process_rss_bytes: 1 << 20,
            // A candidate trying to report its own (fake) timing.
            stdout_trunc: b"wall_ns=1\ntime: 0.000001s\n".to_vec(),
            stderr_trunc: vec![],
            stdout_bytes: 26,
            stderr_bytes: 0,
            outputs: vec![],
            outputs_tree: None,
            output_error: None,
            pids_limit_hit: false,
            limits: LimitEnforcement::CgroupV2,
            isolation: "scripted".into(),
            tier_cap: None,
            entry_wall_ns: Some(1),
            diagnostics: Diagnostics::default(),
            violations: vec![],
        })
    }
}

fn procedure(cold: u32, warm: u32, measured: u32) -> MeasurementProcedure {
    MeasurementProcedure {
        warmup_runs: warm,
        measured_runs: measured,
        aggregation: "median".into(),
        outlier_mad_k: 5,
        cold_runs: cold,
        concurrency: 1,
        per_run_timeout_ms: 1000,
        invocation_mode: None,
    }
}

#[test]
fn session_uses_supervisor_wall_time_only() {
    // 1 cold, 1 warmup, 5 measured, 1 fresh = 8 runs for one class.
    let walls = vec![900, 600, 500, 510, 490, 505, 2000, 520];
    let sb = Scripted {
        walls: Mutex::new(walls),
        calls: Mutex::new(vec![]),
    };
    let mut runner = SpecRunner {
        sandbox: &sb,
        make_spec: |c: &str, p: Phase, r: u32| {
            SandboxSpec::new(vec![format!("{c}:{}:{r}", p.as_str())])
        },
    };
    let plan = SessionPlan {
        classes: vec![ClassPlan {
            class_id: "a".into(),
            weight_ppm: 1_000_000,
            baseline_ns: 1000,
        }],
        procedure: procedure(1, 1, 5),
        schedule_seed: 7,
        bootstrap_seed: 1,
        bootstrap_iterations: 100,
        fresh_confirm_runs: 1,
    };
    let r = run_session(&plan, &mut runner).unwrap();
    let c = &r.classes[0];
    assert_eq!(c.cold_runs_ns, [900]);
    assert_eq!(c.warmup_runs_ns, [600]);
    assert_eq!(c.measured_runs_ns, [500, 510, 490, 505, 2000]);
    assert_eq!(c.fresh_runs_ns, [520]);
    let m = c.to_measurement();
    assert_eq!(m.median_ns, 505);
    assert_eq!(m.mad_ns, 5);
    assert_eq!(m.cold_ns, Some(900));
    // 2000 is flagged but kept.
    assert_eq!(c.outliers.as_ref().unwrap().flagged_indices, [4]);
    let s = r.score.unwrap();
    assert_eq!(s.score_milli, 198_020); // 100 * 1000/505
    assert!(r.flags.is_empty());
    assert_eq!(sb.calls.lock().unwrap()[0], "a:cold:0");
}

#[test]
fn timeout_fails_session_fast() {
    let sb = Scripted {
        walls: Mutex::new(vec![100, 0, 100]),
        calls: Mutex::new(vec![]),
    };
    let mut runner = SpecRunner {
        sandbox: &sb,
        make_spec: |_: &str, _: Phase, _: u32| SandboxSpec::new(vec!["x".into()]),
    };
    let plan = SessionPlan {
        classes: vec![ClassPlan {
            class_id: "a".into(),
            weight_ppm: 1_000_000,
            baseline_ns: 1000,
        }],
        procedure: procedure(0, 0, 3),
        schedule_seed: 1,
        bootstrap_seed: 1,
        bootstrap_iterations: 10,
        fresh_confirm_runs: 0,
    };
    match run_session(&plan, &mut runner) {
        Err(SessionError::Run {
            seq: 1,
            error: RunError::Candidate { reason, .. },
            ..
        }) => {
            assert_eq!(reason, arena_types::ReasonCode::Timeout)
        }
        other => panic!("{other:?}"),
    }
    assert_eq!(sb.calls.lock().unwrap().len(), 2);
}

#[test]
fn caching_tripwire_flags() {
    let walls = vec![100, 101, 99, 100, 100, 200];
    let sb = Scripted {
        walls: Mutex::new(walls),
        calls: Mutex::new(vec![]),
    };
    let mut runner = SpecRunner {
        sandbox: &sb,
        make_spec: |_: &str, _: Phase, _: u32| SandboxSpec::new(vec!["x".into()]),
    };
    let plan = SessionPlan {
        classes: vec![ClassPlan {
            class_id: "a".into(),
            weight_ppm: 1_000_000,
            baseline_ns: 1000,
        }],
        procedure: procedure(0, 0, 5),
        schedule_seed: 1,
        bootstrap_seed: 1,
        bootstrap_iterations: 10,
        fresh_confirm_runs: 1,
    };
    let r = run_session(&plan, &mut runner).unwrap();
    assert!(
        r.flags.contains(&"CACHING_SUSPECTED:a".to_string()),
        "{:?}",
        r.flags
    );
}

#[test]
fn rejects_bad_procedures() {
    let mut p = procedure(0, 0, 3);
    p.concurrency = 2;
    assert!(check_procedure(&p).is_err());
    let mut p = procedure(0, 0, 3);
    p.aggregation = "mean".into();
    assert!(check_procedure(&p).is_err());
    assert!(check_procedure(&procedure(0, 0, 0)).is_err());
}

/// A batch runner that proves and verifies 2 requests per batch plus an
/// untimed warm-up proof (vm_per_batch shape), with scripted times.
struct TwoPerBatch {
    sb: Scripted,
    n: u64,
}

impl BatchRunner for TwoPerBatch {
    fn run_batch(&mut self, _c: &str, _p: Phase, _r: u32) -> Result<BatchSample, RunError> {
        let mut s = BatchSample::default();
        let out = |w: u64| {
            self.sb
                .run(&SandboxSpec::new(vec![format!("{w}")]))
                .unwrap()
        };
        // untimed warm-up proof: counts for max_proof_bytes only
        s.note_proof_bytes(1_000_000);
        for i in 0..2 {
            self.n += 1;
            let mut o = out(0);
            o.wall_ns = 100 + self.n;
            s.push_prove(&o);
            s.note_timed_proof_bytes(1_000 + i);
            o.wall_ns = 10 * self.n;
            s.push_verify(&o);
        }
        Ok(s)
    }
}

#[test]
fn per_run_verify_and_byte_totals_for_cost_scoring() {
    let sb = Scripted {
        walls: Mutex::new(vec![1; 64]),
        calls: Mutex::new(vec![]),
    };
    let mut runner = TwoPerBatch { sb, n: 0 };
    let plan = SessionPlan {
        classes: vec![ClassPlan {
            class_id: "a".into(),
            weight_ppm: 1_000_000,
            baseline_ns: 1000,
        }],
        procedure: procedure(0, 1, 3),
        schedule_seed: 7,
        bootstrap_seed: 1,
        bootstrap_iterations: 10,
        fresh_confirm_runs: 0,
    };
    let r = run_session(&plan, &mut runner).unwrap();
    let c = &r.classes[0];
    // run k (k = 0 warm-up, 1..3 measured) proves requests n = 2k+1, 2k+2
    assert_eq!(c.measured_runs_ns, [207, 211, 215]);
    assert_eq!(c.measured_verify_runs_ns, [70, 110, 150]);
    assert_eq!(c.measured_proof_bytes_runs, [2001, 2001, 2001]);
    assert_eq!(c.verify_runs_ns.len(), 6);
    assert_eq!(c.proof_bytes_max, 1_000_000);
    let m = c.to_measurement();
    assert_eq!(m.verify_runs_ns, [70, 110, 150]);
    assert_eq!(m.proof_bytes_runs, [2001, 2001, 2001]);
}
