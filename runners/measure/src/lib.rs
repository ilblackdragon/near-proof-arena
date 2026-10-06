//! Trusted measurement harness (docs/BENCHMARK_SPEC.md §3–§8).
//!
//! The harness drives a seeded, recorded schedule of batch runs
//! ([`stats::build_schedule`]), takes every time **only** from
//! [`SandboxOutcome::wall_ns`](arena_sandbox::SandboxOutcome) (the
//! supervisor clock; nothing the candidate prints or writes is read), and
//! computes medians, MADs, outlier flags, the caching tripwire and the score
//! with its bootstrap CI ([`score`]).
//!
//! What a "batch run" is (prove each request, check claim, verify) is the
//! worker's business; it plugs in through [`BatchRunner`], building each
//! [`BatchSample`] from sandbox outcomes via [`BatchSample::push_prove`] /
//! [`BatchSample::push_verify`].

pub mod cost;
pub mod score;
pub mod stats;

use arena_sandbox::{ExitStatus, Sandbox, SandboxOutcome, SandboxSpec};
use arena_types::challenge::MeasurementProcedure;
use arena_types::{ClassMeasurement, ReasonCode};
use serde::{Deserialize, Serialize};
use stats::{Phase, ScheduleShape, ScheduledRun};

/// Timings of one batch run, assembled exclusively from sandbox outcomes.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BatchSample {
    prove_wall_ns: Vec<u64>,
    verify_wall_ns: Vec<u64>,
    pub proof_bytes_max: u64,
    /// Σ proof bytes of the batch's timed proofs (cost_v1, §14).
    pub proof_bytes_total: u64,
    pub peak_rss_bytes: u64,
}

impl BatchSample {
    pub fn push_prove(&mut self, o: &SandboxOutcome) {
        self.prove_wall_ns.push(o.wall_ns);
        self.peak_rss_bytes = self.peak_rss_bytes.max(o.peak_rss_bytes);
    }
    pub fn push_verify(&mut self, o: &SandboxOutcome) {
        self.verify_wall_ns.push(o.wall_ns);
    }
    /// Every proof (also untimed warm-up ones) counts for `max_proof_bytes`.
    pub fn note_proof_bytes(&mut self, n: u64) {
        self.proof_bytes_max = self.proof_bytes_max.max(n);
    }
    /// A proof of a timed invocation: also counted in the batch's total
    /// (the bytes term of the cost score, §14).
    pub fn note_timed_proof_bytes(&mut self, n: u64) {
        self.note_proof_bytes(n);
        self.proof_bytes_total = self.proof_bytes_total.saturating_add(n);
    }
    /// Σ verify wall ns of the batch's timed proofs.
    pub fn total_verify_ns(&self) -> u64 {
        self.verify_wall_ns.iter().sum()
    }
    /// `T_run = Σ wall_ns` of the batch's prove invocations (§7.1).
    pub fn total_prove_ns(&self) -> u64 {
        self.prove_wall_ns.iter().sum()
    }
    pub fn prove_wall_ns(&self) -> &[u64] {
        &self.prove_wall_ns
    }
    pub fn verify_wall_ns(&self) -> &[u64] {
        &self.verify_wall_ns
    }
}

/// Why a run produced no valid sample.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RunError {
    /// Candidate-caused (claim mismatch, rejected proof, timeout, ...).
    Candidate { reason: ReasonCode, detail: String },
    /// Judge-side problem; the session must be retried.
    Infra(String),
}

pub trait BatchRunner {
    fn run_batch(
        &mut self,
        class_id: &str,
        phase: Phase,
        round: u32,
    ) -> Result<BatchSample, RunError>;
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassPlan {
    pub class_id: String,
    pub weight_ppm: u32,
    pub baseline_ns: u64,
}

#[derive(Clone, Debug)]
pub struct SessionPlan {
    pub classes: Vec<ClassPlan>,
    pub procedure: MeasurementProcedure,
    pub schedule_seed: u64,
    pub bootstrap_seed: u64,
    pub bootstrap_iterations: u32,
    /// Rounds on an unseen batch for the caching tripwire (spec: 1).
    pub fresh_confirm_runs: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassSession {
    pub class_id: String,
    pub weight_ppm: u32,
    pub baseline_ns: u64,
    pub cold_runs_ns: Vec<u64>,
    pub warmup_runs_ns: Vec<u64>,
    pub measured_runs_ns: Vec<u64>,
    pub fresh_runs_ns: Vec<u64>,
    pub verify_runs_ns: Vec<u64>,
    /// Per measured run: Σ verify wall ns of the batch (cost_v1).
    #[serde(default)]
    pub measured_verify_runs_ns: Vec<u64>,
    /// Per measured run: Σ proof bytes of the batch (cost_v1).
    #[serde(default)]
    pub measured_proof_bytes_runs: Vec<u64>,
    pub proof_bytes_max: u64,
    pub peak_rss_bytes: u64,
    pub outliers: Option<stats::OutlierReport>,
    pub tripwire: Option<stats::TripwireResult>,
}

impl ClassSession {
    pub fn to_measurement(&self) -> ClassMeasurement {
        ClassMeasurement {
            abstained: false,
            class_id: self.class_id.clone(),
            weight_ppm: self.weight_ppm,
            runs_ns: self.measured_runs_ns.clone(),
            median_ns: stats::median_u64(&self.measured_runs_ns).unwrap_or(0),
            mad_ns: stats::mad_u64(&self.measured_runs_ns).unwrap_or(0),
            cold_ns: stats::median_u64(&self.cold_runs_ns),
            baseline_ns: self.baseline_ns,
            verify_median_ns: stats::median_u64(&self.verify_runs_ns).unwrap_or(0),
            proof_bytes_max: self.proof_bytes_max,
            peak_rss_bytes: self.peak_rss_bytes,
            verify_runs_ns: self.measured_verify_runs_ns.clone(),
            proof_bytes_runs: self.measured_proof_bytes_runs.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SessionResult {
    pub schedule_seed: u64,
    pub schedule: Vec<ScheduledRun>,
    pub classes: Vec<ClassSession>,
    pub score: Result<score::BootstrapResult, score::ScoreError>,
    /// Session-level flags: `CACHING_SUSPECTED`, `EXCESSIVE_OUTLIERS:<class>`.
    pub flags: Vec<String>,
}

#[derive(Debug, thiserror::Error)]
pub enum SessionError {
    #[error("invalid measurement procedure: {0}")]
    Procedure(String),
    #[error("run {seq} ({phase} {class_id} round {round}) failed: {error:?}")]
    Run {
        seq: usize,
        phase: &'static str,
        class_id: String,
        round: u32,
        error: RunError,
    },
}

/// Check a `MeasurementProcedure` against bench-spec-v1.
pub fn check_procedure(p: &MeasurementProcedure) -> Result<(), SessionError> {
    let bad = |s: &str| Err(SessionError::Procedure(s.into()));
    if p.aggregation != "median" {
        return bad("aggregation must be \"median\"");
    }
    if p.concurrency != 1 {
        return bad("concurrency must be 1");
    }
    if p.measured_runs == 0 {
        return bad("measured_runs must be >= 1");
    }
    if p.outlier_mad_k == 0 {
        return bad("outlier_mad_k must be >= 1");
    }
    Ok(())
}

/// Run a full measurement session. Fails fast on the first failed run: there
/// is no partial credit (§9).
pub fn run_session(
    plan: &SessionPlan,
    runner: &mut dyn BatchRunner,
) -> Result<SessionResult, SessionError> {
    check_procedure(&plan.procedure)?;
    let ids: Vec<String> = plan.classes.iter().map(|c| c.class_id.clone()).collect();
    let shape = ScheduleShape {
        cold_runs: plan.procedure.cold_runs,
        warmup_runs: plan.procedure.warmup_runs,
        measured_runs: plan.procedure.measured_runs,
        fresh_confirm_runs: plan.fresh_confirm_runs,
        // The calibration binary is not wired yet (no governed hosts): no
        // calibration entries are scheduled. See runners/README.md.
        calibration_runs: 0,
    };
    let schedule =
        stats::build_schedule(&ids, plan.schedule_seed, shape).map_err(SessionError::Procedure)?;
    let mut classes: Vec<ClassSession> = plan
        .classes
        .iter()
        .map(|c| ClassSession {
            class_id: c.class_id.clone(),
            weight_ppm: c.weight_ppm,
            baseline_ns: c.baseline_ns,
            cold_runs_ns: vec![],
            warmup_runs_ns: vec![],
            measured_runs_ns: vec![],
            fresh_runs_ns: vec![],
            verify_runs_ns: vec![],
            measured_verify_runs_ns: vec![],
            measured_proof_bytes_runs: vec![],
            proof_bytes_max: 0,
            peak_rss_bytes: 0,
            outliers: None,
            tripwire: None,
        })
        .collect();
    for run in &schedule {
        let sample = runner
            .run_batch(&run.class_id, run.phase, run.round)
            .map_err(|error| SessionError::Run {
                seq: run.seq,
                phase: run.phase.as_str(),
                class_id: run.class_id.clone(),
                round: run.round,
                error,
            })?;
        let cs = classes
            .iter_mut()
            .find(|c| c.class_id == run.class_id)
            .expect("scheduled class exists");
        let t = sample.total_prove_ns();
        match run.phase {
            Phase::Cold => cs.cold_runs_ns.push(t),
            Phase::Warmup => cs.warmup_runs_ns.push(t),
            Phase::Measured => cs.measured_runs_ns.push(t),
            Phase::FreshConfirm => cs.fresh_runs_ns.push(t),
            Phase::CalibrationPre | Phase::CalibrationPost => {}
        }
        // Every proof is verified in every phase; verify timings are
        // reported from steady-state runs only.
        if run.phase == Phase::Measured {
            cs.verify_runs_ns.extend_from_slice(sample.verify_wall_ns());
            cs.measured_verify_runs_ns.push(sample.total_verify_ns());
            cs.measured_proof_bytes_runs.push(sample.proof_bytes_total);
        }
        cs.proof_bytes_max = cs.proof_bytes_max.max(sample.proof_bytes_max);
        cs.peak_rss_bytes = cs.peak_rss_bytes.max(sample.peak_rss_bytes);
    }
    let k = plan.procedure.outlier_mad_k;
    let mut flags = Vec::new();
    for cs in &mut classes {
        cs.outliers = stats::flag_outliers(&cs.measured_runs_ns, k);
        if cs.outliers.as_ref().is_some_and(|o| o.excessive) {
            flags.push(format!("EXCESSIVE_OUTLIERS:{}", cs.class_id));
        }
        cs.tripwire = stats::caching_tripwire(&cs.measured_runs_ns, &cs.fresh_runs_ns, k);
        if cs.tripwire.as_ref().is_some_and(|t| t.suspected) {
            flags.push(format!("CACHING_SUSPECTED:{}", cs.class_id));
        }
    }
    let runs: Vec<score::ClassRuns> = classes
        .iter()
        .map(|c| score::ClassRuns {
            class_id: c.class_id.clone(),
            weight_ppm: c.weight_ppm,
            baseline_ns: c.baseline_ns,
            runs_ns: c.measured_runs_ns.clone(),
        })
        .collect();
    let score = score::bootstrap_ci(&runs, plan.bootstrap_seed, plan.bootstrap_iterations.max(1));
    Ok(SessionResult {
        schedule_seed: plan.schedule_seed,
        schedule,
        classes,
        score,
        flags,
    })
}

/// A [`BatchRunner`] whose batch is a single sandboxed invocation of a spec
/// (e.g. timing an entry point directly). Success is exit 0; the time is
/// the supervisor's `wall_ns`.
pub struct SpecRunner<'a, F: FnMut(&str, Phase, u32) -> SandboxSpec> {
    pub sandbox: &'a dyn Sandbox,
    pub make_spec: F,
}

impl<F: FnMut(&str, Phase, u32) -> SandboxSpec> BatchRunner for SpecRunner<'_, F> {
    fn run_batch(
        &mut self,
        class_id: &str,
        phase: Phase,
        round: u32,
    ) -> Result<BatchSample, RunError> {
        let spec = (self.make_spec)(class_id, phase, round);
        let o = self
            .sandbox
            .run(&spec)
            .map_err(|e| RunError::Infra(e.to_string()))?;
        match o.exit {
            ExitStatus::Exited(0) => {}
            ExitStatus::TimedOut => {
                return Err(RunError::Candidate {
                    reason: ReasonCode::Timeout,
                    detail: "timed out".into(),
                })
            }
            ExitStatus::OomKilled => {
                return Err(RunError::Candidate {
                    reason: ReasonCode::ResourceLimit,
                    detail: "OOM-killed".into(),
                })
            }
            other => {
                return Err(RunError::Candidate {
                    reason: ReasonCode::ProverFailed,
                    detail: format!("{other:?}"),
                })
            }
        }
        let mut s = BatchSample::default();
        s.push_prove(&o);
        Ok(s)
    }
}

/// Re-exported for callers building `BenchmarkResult`s.
pub use arena_types::BenchmarkResult;
