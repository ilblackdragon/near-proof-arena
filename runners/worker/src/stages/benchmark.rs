//! `BENCHMARK` via the trusted measurement harness (`arena-measure`,
//! docs/BENCHMARK_SPEC.md). Classes, weights, batch sizes and the procedure
//! come from the challenge; batches are sampled by the judge's oracle. Every
//! proof produced during the session is claim-checked and verified; one
//! failure means no score. This job owns only the `BENCHMARK` gate: a
//! failed run (wrong claim, rejected proof, resource cap) fails it with the
//! corresponding reason code.

use super::common::{self, Verdict};
use crate::executor::{ExecError, JobRun, StageOut};
use crate::gate::Gate;
use crate::jobs::{ExecJob, RunLimits};
use crate::oracle::{Case, OracleError};
use arena_measure::stats::{derive_seed, Phase};
use arena_measure::{BatchRunner, BatchSample, ClassPlan, RunError, SessionError, SessionPlan};
use arena_types::challenge::InvocationMode;
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
    /// CPUs `verify` is pinned to: `cpus`, or its first
    /// `price_model.verifier_vcpus` (reference validator profile, §14).
    verify_cpus: Option<Vec<u32>>,
    verifier: common::Verifier,
    failure: Option<(ReasonCode, String)>,
    /// Confirmation mode (spec §7.4): every (class, phase, round) proves a
    /// batch never seen before in this job.
    fresh_only: bool,
    oracle: &'r dyn crate::oracle::Oracle,
    chal: &'r arena_types::ChallengeDefinition,
    seeds: crate::oracle::SeedCtx,
    /// Fail-closed protocol-version binding of every request.
    pin: Option<crate::jobs::RequestPin>,
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

impl Runner<'_, '_> {
    /// bench-spec-v1.1 (`vm_per_batch`): the whole batch in one sandbox
    /// instance, preceded by one untimed warm-up invocation on the batch's
    /// first request (must also be valid). Every request is a fresh process
    /// with a wiped scratch and only its own inputs; `T_run` is the sum of
    /// the timed invocations' supervisor wall times. Every proof (warm-up
    /// included) is claim-checked and verified (verifies batched the same way).
    fn run_batch_shared(&mut self, batch: &[Case], phase: Phase) -> Result<BatchSample, RunError> {
        if batch.is_empty() {
            return Ok(BatchSample::default());
        }
        let (bundle, public_dir, limits, entry, cpus, verifier) = (
            self.bundle.clone(),
            self.public_dir.clone(),
            self.limits.clone(),
            self.entry,
            self.cpus.clone(),
            self.verifier.clone(),
        );
        let env = common::EntryEnv {
            bundle: &bundle,
            entry,
            public_dir: &public_dir,
            limits: &limits,
            cpu_set: cpus,
            verifier: &verifier,
        };
        // index 0 = untimed warm-up on batch[0]
        let order: Vec<&Case> = std::iter::once(&batch[0]).chain(batch.iter()).collect();
        let proved = match common::run_prove_batch(self.r, &env, &order) {
            Ok(p) => p,
            Err(e) => return Err(self.exec_err(e)),
        };
        let mut s = BatchSample::default();
        let mut pairs = Vec::with_capacity(order.len());
        for (i, p) in proved.into_iter().enumerate() {
            let case = order[i];
            let label = common::case_label(&case.id, case.public);
            let p = match p {
                Ok(p) => p,
                Err(f) => {
                    return Err(self.fail(
                        f.reason,
                        format!(
                            "{} run, {label}: {}",
                            phase.as_str(),
                            f.detail_for(case.public)
                        ),
                    ))
                }
            };
            cross_check(&p.outcome)?;
            if i > 0 {
                s.push_prove(&p.outcome);
                s.note_timed_proof_bytes(p.proof.len() as u64);
            } else {
                s.note_proof_bytes(p.proof.len() as u64);
            }
            pairs.push((p.claim_path, p.proof_path));
        }
        let venv = common::EntryEnv {
            cpu_set: self.verify_cpus.clone(),
            ..env
        };
        let verified = match common::run_verify_batch(self.r, &venv, &pairs) {
            Ok(v) => v,
            Err(e) => return Err(self.exec_err(e)),
        };
        for (i, (v, vo)) in verified.into_iter().enumerate() {
            let case = order[i];
            let label = common::case_label(&case.id, case.public);
            cross_check(&vo)?;
            match v {
                Verdict::Accept => {
                    if i > 0 {
                        s.push_verify(&vo)
                    }
                }
                Verdict::TimedOut => {
                    return Err(self.fail(
                        ReasonCode::ResourceLimit,
                        format!("{label}: verify exceeded max_verify_ms"),
                    ))
                }
                Verdict::BindingMismatch => {
                    return Err(self.fail(
                        ReasonCode::ArtifactBindingFailed,
                        "npai-verify: the verifier bytecode is not the certified image".into(),
                    ))
                }
                _ => {
                    return Err(self.fail(
                        ReasonCode::ProverFailed,
                        format!(
                            "{} run, {label}: verify did not accept the proof",
                            phase.as_str()
                        ),
                    ))
                }
            }
        }
        Ok(s)
    }
}

/// Host-side sanity check of a timing: when the backend reports the VMM's
/// own wall time, the candidate's wall time must fit inside it.
fn cross_check(o: &arena_sandbox::SandboxOutcome) -> Result<(), RunError> {
    let vmm = o.diagnostics.vmm_wall_ns;
    if vmm > 0 && o.wall_ns > vmm {
        return Err(RunError::Infra(format!(
            "timing cross-check failed: wall {} ns > VMM wall {} ns",
            o.wall_ns, vmm
        )));
    }
    Ok(())
}

impl BatchRunner for Runner<'_, '_> {
    fn run_batch(
        &mut self,
        class_id: &str,
        phase: Phase,
        round: u32,
    ) -> Result<BatchSample, RunError> {
        let (batch, fresh) = self.batches[class_id].clone();
        let batch = if self.fresh_only {
            let tag = format!("{class_id}#confirm-{}-{round}", phase.as_str());
            self.oracle
                .sample(self.chal, class_id, &self.seeds.tagged(&tag), batch.len())
                .map_err(|e| RunError::Infra(e.to_string()))?
        } else if phase == Phase::FreshConfirm {
            fresh
        } else {
            batch
        };
        if let Some(pin) = &self.pin {
            for c in &batch {
                common::check_case_pin(pin, c).map_err(|e| RunError::Infra(e.to_string()))?;
            }
        }
        if phase != Phase::Cold
            && self.chal.measurement.invocation_mode() == InvocationMode::VmPerBatch
        {
            return self.run_batch_shared(&batch, phase);
        }
        let mut s = BatchSample::default();
        for case in &batch {
            let label = common::case_label(&case.id, case.public);
            let (bundle, public_dir, limits, entry, cpus, verifier) = (
                self.bundle.clone(),
                self.public_dir.clone(),
                self.limits.clone(),
                self.entry,
                self.cpus.clone(),
                self.verifier.clone(),
            );
            let env = common::EntryEnv {
                bundle: &bundle,
                entry,
                public_dir: &public_dir,
                limits: &limits,
                cpu_set: cpus,
                verifier: &verifier,
            };
            let p = match common::run_prove(self.r, &env, case) {
                Err(e) => return Err(self.exec_err(e)),
                Ok(Err(f)) => {
                    return Err(self.fail(
                        f.reason,
                        format!(
                            "{} run, {label}: {}",
                            phase.as_str(),
                            f.detail_for(case.public)
                        ),
                    ))
                }
                Ok(Ok(p)) => p,
            };
            cross_check(&p.outcome)?;
            s.push_prove(&p.outcome);
            s.note_timed_proof_bytes(p.proof.len() as u64);
            let venv = common::EntryEnv {
                cpu_set: self.verify_cpus.clone(),
                ..env
            };
            let (v, vo) = match common::run_verify(self.r, &venv, &p.claim_path, &p.proof_path) {
                Ok(x) => x,
                Err(e) => return Err(self.exec_err(e)),
            };
            cross_check(&vo)?;
            match v {
                Verdict::Accept => s.push_verify(&vo),
                Verdict::TimedOut => {
                    return Err(self.fail(
                        ReasonCode::ResourceLimit,
                        format!("{label}: verify exceeded max_verify_ms"),
                    ))
                }
                Verdict::BindingMismatch => {
                    return Err(self.fail(
                        ReasonCode::ArtifactBindingFailed,
                        "npai-verify: the verifier bytecode is not the certified image".into(),
                    ))
                }
                _ => {
                    return Err(self.fail(
                        ReasonCode::ProverFailed,
                        format!(
                            "{} run, {label}: verify did not accept the proof",
                            phase.as_str()
                        ),
                    ))
                }
            }
        }
        Ok(s)
    }
}

pub fn run(r: &mut JobRun<'_>, j: &ExecJob) -> Result<StageOut, ExecError> {
    let mut bench = Gate::start(ObligationId::Benchmark);
    let mut out = StageOut {
        used_sandbox: true,
        ..Default::default()
    };
    let chal = &j.challenge;
    arena_measure::check_procedure(&chal.measurement)
        .map_err(|e| ExecError::Infra(e.to_string()))?;
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
    let seeds = crate::executor::seeds(r.ctx, &j.ctx);
    bench.note(seeds.mode());
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
        let batch = oracle
            .sample(chal, &c.id, &seeds, n)
            .map_err(|e| ExecError::Infra(e.to_string()))?;
        if batch.len() < n {
            return Err(ExecError::Infra(format!(
                "fail-closed: class {:?}: oracle sampled {} of the {n} batch members",
                c.id,
                batch.len()
            )));
        }
        let fresh_tag = format!("{}#fresh", c.id);
        let fresh = oracle
            .sample(chal, &c.id, &seeds.tagged(&fresh_tag), n)
            .map_err(|e| ExecError::Infra(e.to_string()))?;
        batches.insert(c.id.clone(), (batch, fresh));
    }
    let bundle = common::fetch_bundle(r, &j.build, &j.manifest.entry)?;
    let public_dir = common::fetch_public(r, &j.build, &limits)?;
    let verifier = match common::verifier_for(r, j, &bundle, false)? {
        Ok(v) => v,
        Err(why) => {
            bench.note(why);
            out.gates.push(bench.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
    };
    // `prepare` is timed (reported, never scored) on the frozen bundle.
    let params = common::approved_params(r, chal)?;
    let prepare_ns = match common::run_prepare(r, &bundle, &j.manifest.entry, &limits, &params)? {
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
    let public_bytes =
        arena_archive::tree_from_dir(&public_dir, &arena_archive::Limits::default())?.total_bytes();

    let baselines: HashMap<&str, u64> = chal
        .workload_suite
        .baseline_ns
        .iter()
        .map(|(k, v)| (k.as_str(), *v))
        .collect();
    let plan = SessionPlan {
        classes: chal
            .workload_suite
            .classes
            .iter()
            .map(|c| ClassPlan {
                class_id: c.id.clone(),
                weight_ppm: c.weight_ppm,
                baseline_ns: baselines.get(c.id.as_str()).copied().unwrap_or(0),
            })
            .collect(),
        procedure: chal.measurement.clone(),
        schedule_seed: derive_seed(
            "schedule",
            &[&j.ctx.challenge_id, &j.ctx.submission_id, &j.ctx.run_id],
        )
        .map_err(ExecError::Infra)?,
        bootstrap_seed: derive_seed("bootstrap", &[&j.ctx.submission_id, &j.ctx.run_id])
            .map_err(ExecError::Infra)?,
        bootstrap_iterations: BOOTSTRAP_ITERATIONS,
        fresh_confirm_runs: 1,
    };
    let cpus = r.ctx.bench_cpus.clone();
    let verify_cpus = verify_cpu_set(chal, cpus.as_ref()).map_err(ExecError::Infra)?;
    let worker_id = r.ctx.worker_id.clone();
    let mut runner = Runner {
        r,
        entry: &j.manifest.entry,
        limits: limits.clone(),
        bundle,
        public_dir,
        batches,
        cpus,
        verify_cpus,
        verifier,
        failure: None,
        fresh_only: false,
        oracle,
        chal,
        seeds: seeds.clone(),
        pin: crate::jobs::RequestPin::from_challenge(chal),
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
            Err(SessionError::Run {
                error: RunError::Infra(e),
                ..
            }) => return Err(ExecError::Infra(e)),
            Err(SessionError::Run {
                error: RunError::Candidate { .. },
                ..
            }) => {
                let (reason, detail) = failure.expect("candidate failure recorded");
                bench.fail(reason, format!("no score: {detail}"));
                out.gates.push(bench.finish(GateStatus::Unknown, true));
                return Ok(out);
            }
            Err(e) => return Err(ExecError::Infra(e.to_string())),
        };
        if !runner.fresh_only
            && session
                .flags
                .iter()
                .any(|f| f.starts_with("CACHING_SUSPECTED"))
        {
            // §7.4: the number is only published after a re-run on fresh
            // batches only (every round a new batch); that run's number is
            // the published one. A candidate that caches across runs stays
            // slow there (no seen inputs exist).
            bench.note(format!(
                "session {attempt}: CACHING_SUSPECTED; re-measured on fresh batches only"
            ));
            runner.fresh_only = true;
            plan.fresh_confirm_runs = 0;
            attempt = 0;
            continue;
        }
        match session
            .flags
            .iter()
            .find(|f| f.starts_with("EXCESSIVE_OUTLIERS"))
        {
            None => break session,
            Some(f) if attempt >= MAX_SESSIONS => {
                return Err(ExecError::Infra(format!(
                    "{f} in {attempt} sessions: host too noisy"
                )))
            }
            Some(f) => bench.note(format!("session {attempt} discarded ({f}); re-measured")),
        }
    };
    let r = runner.r;
    let classes: Vec<_> = session.classes.iter().map(|c| c.to_measurement()).collect();
    // Resource caps over every measured run.
    for c in &classes {
        if c.proof_bytes_max > limits.max_proof_bytes {
            bench.fail(
                ReasonCode::ResourceLimit,
                format!(
                    "class {}: proof {} bytes > max_proof_bytes",
                    c.class_id, c.proof_bytes_max
                ),
            );
        }
        if c.peak_rss_bytes > limits.max_ram_bytes {
            bench.fail(
                ReasonCode::ResourceLimit,
                format!(
                    "class {}: peak memory {} > max_ram_bytes",
                    c.class_id, c.peak_rss_bytes
                ),
            );
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
    let cost = match cost_result(chal, &classes, prepare_ns, &plan) {
        Ok(c) => c,
        Err(e) => {
            bench.note(format!("cost_v1 score not computed: {e}"));
            None
        }
    };
    let mut measured_by = format!("arena-worker {worker_id}");
    if capped {
        measured_by.push_str(" [DEV: batch sizes capped]");
        bench.note(format!(
            "DEV: batch sizes capped at {} (timings not comparable)",
            r.ctx.bench_batch_cap.unwrap_or(0)
        ));
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
        cost,
    };
    let report = serde_json::json!({
        "invocation_mode": chal.measurement.invocation_mode(),
        "sandbox_instance_per_batch": chal.measurement.invocation_mode() == InvocationMode::VmPerBatch
            && r.ctx.sandbox.steps_share_instance(),
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
    if let Some(c) = &result.cost {
        bench.note(format!(
            "cost_v1 ({}, N_v={}, verify on {} vCPUs): score {} ± {} milli",
            c.price_model_id,
            c.validators_per_chunk,
            c.verifier_vcpus,
            c.score_milli.unwrap_or(0),
            c.score_ci_milli.unwrap_or(0)
        ));
    }
    if bench.failed() {
        out.gates.push(bench.finish(GateStatus::Unknown, true));
        return Ok(out);
    }
    if session
        .flags
        .iter()
        .any(|f| f.starts_with("CACHING_SUSPECTED"))
    {
        bench.note("CACHING_SUSPECTED: fresh-input batch markedly slower; re-run with fresh batches before ranking");
        out.gates.push(bench.finish(GateStatus::Unknown, true));
    } else {
        if let (Some(s), Some(c)) = (score_milli, ci) {
            bench.note(format!(
                "worker-side score {s} ± {c} milli (server recomputes)"
            ));
        }
        out.gates.push(bench.finish(GateStatus::Pass, true));
    }
    out.benchmark = Some(result);
    Ok(out)
}

/// The CPUs `verify` runs on: the benchmark set, or (cost_v1) its first
/// `verifier_vcpus` — the reference validator profile is measured, not
/// assumed. Fail closed if the benchmark set is too small or unset.
fn verify_cpu_set(
    chal: &arena_types::ChallengeDefinition,
    cpus: Option<&Vec<u32>>,
) -> Result<Option<Vec<u32>>, String> {
    let Some(pm) = chal.scoring.as_ref().and_then(|s| s.price_model.as_ref()) else {
        return Ok(cpus.cloned());
    };
    let k = pm.verifier_vcpus as usize;
    match cpus {
        Some(c) if c.len() >= k => Ok(Some(c[..k].to_vec())),
        Some(c) => Err(format!(
            "fail-closed: cost_v1 verifies on {k} vCPUs but the benchmark CPU set has {}",
            c.len()
        )),
        None => Err("fail-closed: cost_v1 needs a pinned benchmark CPU set".into()),
    }
}

/// cost_v1 score (point + seeded bootstrap CI) of a session; `None` for
/// speed-only challenges.
fn cost_result(
    chal: &arena_types::ChallengeDefinition,
    classes: &[arena_types::ClassMeasurement],
    prepare_ns: u64,
    plan: &SessionPlan,
) -> Result<Option<arena_types::CostResult>, String> {
    let Some(sc) = chal.scoring.as_ref() else {
        return Ok(None);
    };
    if sc.kind != arena_types::ScoringKind::CostV1 {
        return Ok(None);
    }
    chal.check_scoring()?;
    let pm = sc.price_model.as_ref().expect("checked");
    let digest = sc.price_model_digest.clone().expect("checked");
    let prices = arena_measure::cost::Prices::for_scoring(sc, pm, chal.hardware_profile.vcpus);
    let runs = arena_measure::cost::class_runs_for(chal, classes).map_err(|e| e.to_string())?;
    let base_prep = sc.cost_baseline_prepare_ns.unwrap_or(0);
    let point = arena_measure::cost::cost_score(&prices, &runs, prepare_ns, base_prep)
        .map_err(|e| e.code().to_string())?;
    // Same seed as the speed bootstrap (§14.3): independent computation.
    let seed = plan.bootstrap_seed;
    let ci = arena_measure::cost::cost_bootstrap(
        &prices,
        &runs,
        prepare_ns,
        base_prep,
        seed,
        plan.bootstrap_iterations.max(1),
    )
    .map_err(|e| e.code().to_string())?;
    Ok(Some(arena_measure::cost::to_contract(
        pm,
        digest,
        &point,
        Some(ci.half_width_milli),
    )))
}

#[cfg(test)]
mod tests {
    use super::verify_cpu_set;

    fn chal(verifier_vcpus: Option<u32>) -> arena_types::ChallengeDefinition {
        let mut c: arena_types::ChallengeDefinition = serde_json::from_str(include_str!(
            "../../../../challenges/chl_7c0456cb2d1a36f8601863ac206cfcc9.json"
        ))
        .unwrap();
        if let Some(k) = verifier_vcpus {
            let mut pm: arena_types::PriceModel = serde_json::from_str(include_str!(
                "../../../../challenges/price-models/pm-near-mainnet-2026q4.draft.json"
            ))
            .unwrap();
            pm.verifier_vcpus = k;
            c.scoring = Some(arena_types::ScoringSpec {
                kind: arena_types::ScoringKind::CostV1,
                price_model_digest: Some(pm.digest().unwrap()),
                price_model: Some(pm),
                cost_baseline: vec![],
                cost_baseline_prepare_ns: None,
                verify_statistic: None,
            });
        }
        c
    }

    #[test]
    fn verify_runs_on_the_reference_validator_profile() {
        let cpus: Vec<u32> = (0..8).collect();
        // speed challenge: verify on the benchmark set, unchanged
        assert_eq!(
            verify_cpu_set(&chal(None), Some(&cpus)).unwrap(),
            Some(cpus.clone())
        );
        assert_eq!(verify_cpu_set(&chal(None), None).unwrap(), None);
        // cost_v1: the first verifier_vcpus benchmark CPUs
        assert_eq!(
            verify_cpu_set(&chal(Some(2)), Some(&cpus)).unwrap(),
            Some(vec![0, 1])
        );
        // fail closed when the profile cannot be pinned
        assert!(verify_cpu_set(&chal(Some(9)), Some(&cpus)).is_err());
        assert!(verify_cpu_set(&chal(Some(2)), None).is_err());
    }
}
