//! `BENCHMARK` via the trusted measurement harness (`arena-measure`,
//! docs/BENCHMARK_SPEC.md). Classes, weights, batch sizes and the procedure
//! come from the challenge; batches are sampled by the judge's oracle. Every
//! proof produced during the session is claim-checked and verified; one
//! failure means no score. This job owns only the `BENCHMARK` gate: a
//! failed run (wrong claim, rejected proof, resource cap) fails it with the
//! corresponding reason code.

use super::common::{self, Verdict};
use crate::executor::{seed_parts, ExecError, JobRun, StageOut};
use crate::gate::Gate;
use crate::jobs::{ExecJob, RunLimits};
use crate::oracle::{Case, OracleError};
use arena_measure::stats::{derive_seed, Phase};
use arena_measure::{BatchRunner, BatchSample, ClassPlan, RunError, SessionError, SessionPlan};
use arena_types::{BenchmarkResult, GateStatus, ObligationId, ReasonCode};
use std::collections::HashMap;
use std::path::PathBuf;

const MAX_SESSIONS: u32 = 3;
const BOOTSTRAP_ITERATIONS: u32 = arena_measure::score::DEFAULT_BOOTSTRAP_ITERATIONS;

struct Runner<'r, 'a> {
    r: &'r mut JobRun<'a>,
    entry: &'r arena_types::candidate::EntrySection,
    limits: RunLimits,
    bundle: PathBuf,
    public_dir: PathBuf,
    batches: HashMap<String, (Vec<Case>, Vec<Case>)>,
    cpus: Option<Vec<u32>>,
    failure: Option<(ReasonCode, String)>,
    /// Confirmation mode (spec §7.4): every (class, phase, round) proves a
    /// batch never seen before in this job.
    fresh_only: bool,
    oracle: &'r dyn crate::oracle::Oracle,
    chal: &'r arena_types::ChallengeDefinition,
    parts: Vec<String>,
}

impl Runner<'_, '_> {
    fn fail(&mut self, reason: ReasonCode, detail: String) -> RunError {
        self.failure = Some((reason, detail.clone()));
        RunError::Candidate { reason, detail }
    }
    fn exec_err(&mut self, e: ExecError) -> RunError {
        match e {
            ExecError::Violation(m) => self.fail(ReasonCode::SandboxViolation, m),
            e => RunError::Infra(e.to_string()),
        }
    }
}

/// Host-side sanity check of a timing: when the backend reports the VMM's
/// own wall time, the candidate's wall time must fit inside it.
fn cross_check(o: &arena_sandbox::SandboxOutcome) -> Result<(), RunError> {
    let vmm = o.diagnostics.vmm_wall_ns;
    if vmm > 0 && o.wall_ns > vmm {
        return Err(RunError::Infra(format!("timing cross-check failed: wall {} ns > VMM wall {} ns", o.wall_ns, vmm)));
    }
    Ok(())
}

impl BatchRunner for Runner<'_, '_> {
    fn run_batch(&mut self, class_id: &str, phase: Phase, round: u32) -> Result<BatchSample, RunError> {
        let (batch, fresh) = self.batches[class_id].clone();
        let batch = if self.fresh_only {
            let tag = format!("{class_id}#confirm-{}-{round}", phase.as_str());
            let mut parts: Vec<&str> = self.parts.iter().map(|s| s.as_str()).collect();
            parts.push(&tag);
            self.oracle.sample(self.chal, class_id, &parts, batch.len()).map_err(|e| RunError::Infra(e.to_string()))?
        } else if phase == Phase::FreshConfirm {
            fresh
        } else {
            batch
        };
        let mut s = BatchSample::default();
        for case in &batch {
            let label = common::case_label(&case.id, case.public);
            let (bundle, public_dir, limits, entry, cpus) = (self.bundle.clone(), self.public_dir.clone(), self.limits.clone(), self.entry, self.cpus.clone());
            let env = common::EntryEnv { bundle: &bundle, entry, public_dir: &public_dir, limits: &limits, cpu_set: cpus };
            let p = match common::run_prove(self.r, &env, case) {
                Err(e) => return Err(self.exec_err(e)),
                Ok(Err(f)) => return Err(self.fail(f.reason, format!("{} run, {label}: {}", phase.as_str(), f.detail))),
                Ok(Ok(p)) => p,
            };
            cross_check(&p.outcome)?;
            s.push_prove(&p.outcome);
            s.note_proof_bytes(p.proof.len() as u64);
            let (v, vo) = match common::run_verify(self.r, &env, &p.claim_path, &p.proof_path) {
                Ok(x) => x,
                Err(e) => return Err(self.exec_err(e)),
            };
            cross_check(&vo)?;
            match v {
                Verdict::Accept => s.push_verify(&vo),
                Verdict::TimedOut => return Err(self.fail(ReasonCode::ResourceLimit, format!("{label}: verify exceeded max_verify_ms"))),
                _ => return Err(self.fail(ReasonCode::ProverFailed, format!("{} run, {label}: verify did not accept the proof", phase.as_str()))),
            }
        }
        Ok(s)
    }
}

pub fn run(r: &mut JobRun<'_>, j: &ExecJob) -> Result<StageOut, ExecError> {
    let mut bench = Gate::start(ObligationId::Benchmark);
    let mut out = StageOut { used_sandbox: true, ..Default::default() };
    let chal = &j.challenge;
    arena_measure::check_procedure(&chal.measurement).map_err(|e| ExecError::Infra(e.to_string()))?;
    if let Some(why) = common::unsupported_verify_route(&j.manifest.entry) {
        bench.note(why);
        out.gates.push(bench.finish(GateStatus::Unknown, true));
        return Ok(out);
    }
    let limits = RunLimits::from_challenge(chal);
    let oracle = match r.ctx.oracles.get(chal) {
        Ok(o) => o,
        Err(OracleError::Unavailable(m)) => {
            bench.note(m);
            out.gates.push(bench.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
        Err(e) => return Err(ExecError::Infra(e.to_string())),
    };
    let parts_owned = seed_parts(&j.ctx);
    let parts: Vec<&str> = parts_owned.iter().map(|s| s.as_str()).collect();
    let mut batches = HashMap::new();
    let mut capped = false;
    for c in &chal.workload_suite.classes {
        let mut n = c.batch_size as usize;
        if let Some(cap) = r.ctx.bench_batch_cap {
            if n > cap as usize {
                n = cap as usize;
                capped = true;
            }
        }
        let batch = oracle.sample(chal, &c.id, &parts, n).map_err(|e| ExecError::Infra(e.to_string()))?;
        let fresh_tag = format!("{}#fresh", c.id);
        let mut fresh_parts = parts.clone();
        fresh_parts.push(&fresh_tag);
        let fresh = oracle.sample(chal, &c.id, &fresh_parts, n).map_err(|e| ExecError::Infra(e.to_string()))?;
        batches.insert(c.id.clone(), (batch, fresh));
    }
    let bundle = common::fetch_bundle(r, &j.build, &j.manifest.entry)?;
    let public_dir = common::fetch_public(r, &j.build, &limits)?;
    // `prepare` is timed (reported, never scored) on the frozen bundle.
    let prepare_ns = match common::run_prepare(r, &bundle, &j.manifest.entry, &limits)? {
        Ok(p) => {
            if p.tree.digest() != j.build.public_artifacts {
                bench.note("judge re-run of prepare produced a different public dir; the frozen one is used");
            }
            p.outcome.wall_ns
        }
        Err(f) => {
            bench.fail(f.reason, format!("prepare: {}", f.detail));
            out.gates.push(bench.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
    };
    let public_bytes = arena_archive::tree_from_dir(&public_dir, &arena_archive::Limits::default())?.total_bytes();

    let baselines: HashMap<&str, u64> = chal.workload_suite.baseline_ns.iter().map(|(k, v)| (k.as_str(), *v)).collect();
    let plan = SessionPlan {
        classes: chal
            .workload_suite
            .classes
            .iter()
            .map(|c| ClassPlan { class_id: c.id.clone(), weight_ppm: c.weight_ppm, baseline_ns: baselines.get(c.id.as_str()).copied().unwrap_or(0) })
            .collect(),
        procedure: chal.measurement.clone(),
        schedule_seed: derive_seed("schedule", &[&j.ctx.challenge_id, &j.ctx.submission_id, &j.ctx.run_id]).map_err(ExecError::Infra)?,
        bootstrap_seed: derive_seed("bootstrap", &[&j.ctx.submission_id, &j.ctx.run_id]).map_err(ExecError::Infra)?,
        bootstrap_iterations: BOOTSTRAP_ITERATIONS,
        fresh_confirm_runs: 1,
    };
    let cpus = r.ctx.bench_cpus.clone();
    let worker_id = r.ctx.worker_id.clone();
    let mut runner = Runner {
        r,
        entry: &j.manifest.entry,
        limits: limits.clone(),
        bundle,
        public_dir,
        batches,
        cpus,
        failure: None,
        fresh_only: false,
        oracle,
        chal,
        parts: parts_owned.to_vec(),
    };
    let mut plan = plan;
    // A session with too many outliers is re-measured as a whole (spec
    // §7.3), up to MAX_SESSIONS times within the job, then an infra error.
    let mut attempt = 0;
    let session = loop {
        attempt += 1;
        let session = arena_measure::run_session(&plan, &mut runner);
        let failure = runner.failure.take();
        let session = match session {
            Ok(s) => s,
            Err(SessionError::Run { error: RunError::Infra(e), .. }) => return Err(ExecError::Infra(e)),
            Err(SessionError::Run { error: RunError::Candidate { .. }, .. }) => {
                let (reason, detail) = failure.expect("candidate failure recorded");
                bench.fail(reason, format!("no score: {detail}"));
                out.gates.push(bench.finish(GateStatus::Unknown, true));
                return Ok(out);
            }
            Err(e) => return Err(ExecError::Infra(e.to_string())),
        };
        if !runner.fresh_only && session.flags.iter().any(|f| f.starts_with("CACHING_SUSPECTED")) {
            // §7.4: the number is only published after a re-run on fresh
            // batches only (every round a new batch); that run's number is
            // the published one. A candidate that caches across runs stays
            // slow there (no seen inputs exist).
            bench.note(format!("session {attempt}: CACHING_SUSPECTED; re-measured on fresh batches only"));
            runner.fresh_only = true;
            plan.fresh_confirm_runs = 0;
            attempt = 0;
            continue;
        }
        match session.flags.iter().find(|f| f.starts_with("EXCESSIVE_OUTLIERS")) {
            None => break session,
            Some(f) if attempt >= MAX_SESSIONS => return Err(ExecError::Infra(format!("{f} in {attempt} sessions: host too noisy"))),
            Some(f) => bench.note(format!("session {attempt} discarded ({f}); re-measured")),
        }
    };
    let r = runner.r;
    let classes: Vec<_> = session.classes.iter().map(|c| c.to_measurement()).collect();
    // Resource caps over every measured run.
    for c in &classes {
        if c.proof_bytes_max > limits.max_proof_bytes {
            bench.fail(ReasonCode::ResourceLimit, format!("class {}: proof {} bytes > max_proof_bytes", c.class_id, c.proof_bytes_max));
        }
        if c.peak_rss_bytes > limits.max_ram_bytes {
            bench.fail(ReasonCode::ResourceLimit, format!("class {}: peak memory {} > max_ram_bytes", c.class_id, c.peak_rss_bytes));
        }
    }
    let (score_milli, ci) = match &session.score {
        Ok(s) => (Some(s.score_milli), Some(s.half_width_milli)),
        // Unscored suites (no frozen baseline) still get measurements.
        Err(_) if baselines.len() < chal.workload_suite.classes.len() => {
            bench.note("challenge has no frozen baseline for every class: measured, not scored");
            (None, None)
        }
        Err(e) => return Err(ExecError::Infra(format!("score: {}", e.code()))),
    };
    let mut measured_by = format!("arena-worker {worker_id}");
    if capped {
        measured_by.push_str(" [DEV: batch sizes capped]");
        bench.note(format!("DEV: batch sizes capped at {} (timings not comparable)", r.ctx.bench_batch_cap.unwrap_or(0)));
    }
    let result = BenchmarkResult {
        hardware_profile: chal.hardware_profile.id.clone(),
        suite_revision: chal.workload_suite.revision.clone(),
        classes,
        score_milli,
        score_ci_milli: ci,
        prepare_ns,
        public_artifact_bytes: public_bytes,
        measured_by,
    };
    let report = serde_json::json!({
        "schedule_seed": session.schedule_seed,
        "schedule": session.schedule,
        "classes": session.classes,
        "bootstrap": session.score.as_ref().ok(),
        "flags": session.flags,
    });
    let report_bytes = serde_json::to_vec(&report).map_err(|e| ExecError::Infra(e.to_string()))?;
    let d = r.upload("benchmark session", &report_bytes, true)?;
    bench.evidence("benchmark session", d, true);
    for c in &result.classes {
        bench.note(format!(
            "{}: median {} us, MAD {} us, verify median {} us, max proof {} B",
            c.class_id,
            c.median_ns / 1000,
            c.mad_ns / 1000,
            c.verify_median_ns / 1000,
            c.proof_bytes_max
        ));
    }
    if bench.failed() {
        out.gates.push(bench.finish(GateStatus::Unknown, true));
        return Ok(out);
    }
    if session.flags.iter().any(|f| f.starts_with("CACHING_SUSPECTED")) {
        bench.note("CACHING_SUSPECTED: fresh-input batch markedly slower; re-run with fresh batches before ranking");
        out.gates.push(bench.finish(GateStatus::Unknown, true));
    } else {
        if let (Some(s), Some(c)) = (score_milli, ci) {
            bench.note(format!("worker-side score {s} ± {c} milli (server recomputes)"));
        }
        out.gates.push(bench.finish(GateStatus::Pass, true));
    }
    out.benchmark = Some(result);
    Ok(out)
}
