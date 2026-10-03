//! `BENCHMARK` + `RESOURCE_LIMITS` via the trusted measurement harness
//! (`arena-measure`, docs/BENCHMARK_SPEC.md). Every proof produced during
//! the session is claim-checked and verified; one failure means no score.

use super::common::{self, Verdict};
use crate::executor::{ExecError, JobRun, StageOut, MAX_BUNDLE_BYTES};
use crate::gate::Gate;
use crate::jobs::{BenchmarkJob, OracleCase};
use arena_measure::stats::Phase;
use arena_measure::{BatchRunner, BatchSample, ClassPlan, RunError, SessionError, SessionPlan};
use arena_types::{BenchmarkResult, GateStatus, ObligationId, ReasonCode};
use std::collections::HashMap;
use std::path::PathBuf;

struct Runner<'r, 'a> {
    r: &'r mut JobRun<'a>,
    j: &'r BenchmarkJob,
    bundle: PathBuf,
    public_dir: PathBuf,
    inputs: HashMap<String, (PathBuf, PathBuf)>,
    cpus: Option<Vec<u32>>,
    /// The gate a candidate failure belongs to.
    failure: Option<(ObligationId, ReasonCode, String)>,
}

impl Runner<'_, '_> {
    fn fail(&mut self, gate: ObligationId, reason: ReasonCode, detail: String) -> RunError {
        self.failure = Some((gate, reason, detail.clone()));
        RunError::Candidate { reason, detail }
    }
}

impl Runner<'_, '_> {
    fn exec_err(&mut self, e: ExecError) -> RunError {
        match e {
            ExecError::Violation(m) => {
                self.fail(ObligationId::Benchmark, ReasonCode::SandboxViolation, m)
            }
            e => RunError::Infra(e.to_string()),
        }
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
        _round: u32,
    ) -> Result<BatchSample, RunError> {
        let class = self
            .j
            .classes
            .iter()
            .find(|c| c.class_id == class_id)
            .expect("scheduled class");
        let batch: &[OracleCase] = if phase == Phase::FreshConfirm {
            &class.fresh_batch
        } else {
            &class.batch
        };
        let mut s = BatchSample::default();
        for case in batch {
            let label = common::case_label(&case.id, case.public);
            let (req, wit) = self.inputs[&case.id].clone();
            let env = common::EntryEnv {
                bundle: &self.bundle,
                entry: &self.j.entry,
                public_dir: &self.public_dir,
                limits: &self.j.limits,
                cpu_set: self.cpus.clone(),
            };
            let proved = match common::run_prove(self.r, &env, &req, &wit, &case.expected_claim) {
                Ok(p) => p,
                Err(e) => return Err(self.exec_err(e)),
            };
            let p = match proved {
                Ok(p) => p,
                Err(f) => {
                    return Err(self.fail(
                        f.gate,
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
            s.push_prove(&p.outcome);
            s.note_proof_bytes(p.proof.len() as u64);
            let (v, vo) = match common::run_verify(self.r, &env, &p.claim_path, &p.proof_path) {
                Ok(x) => x,
                Err(e) => return Err(self.exec_err(e)),
            };
            cross_check(&vo)?;
            match v {
                Verdict::Accept => s.push_verify(&vo),
                Verdict::TimedOut => {
                    return Err(self.fail(
                        ObligationId::ResourceLimits,
                        ReasonCode::ResourceLimit,
                        format!("{label}: verify exceeded max_verify_ms"),
                    ))
                }
                _ => {
                    return Err(self.fail(
                        ObligationId::ProverReliability,
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

pub fn run(r: &mut JobRun<'_>, j: &BenchmarkJob) -> Result<StageOut, ExecError> {
    let mut bench = Gate::start(ObligationId::Benchmark);
    let mut res = Gate::start(ObligationId::ResourceLimits);
    let mut rel = Gate::start(ObligationId::ProverReliability);
    let mut out = StageOut {
        used_sandbox: true,
        ..Default::default()
    };
    arena_measure::check_procedure(&j.procedure).map_err(|e| ExecError::Infra(e.to_string()))?;
    if j.classes.is_empty() || j.classes.iter().any(|c| c.batch.is_empty()) {
        return Err(ExecError::Infra(
            "benchmark job has an empty class or batch".into(),
        ));
    }
    let bundle = common::fetch_bundle(r, &j.bundle, &j.entry)?;
    let Some(prep) = common::run_prepare(
        r, &bundle, &j.entry, &j.params, &j.limits, &mut rel, &mut res,
    )?
    else {
        bench.note("not run: prepare failed");
        out.gates.push(bench.finish(GateStatus::Unknown, true));
        out.gates.push(res.finish(GateStatus::Unknown, true));
        out.gates.push(rel.finish(GateStatus::Unknown, true));
        return Ok(out);
    };
    let prepare_ns = prep.outcome.wall_ns;
    let public_bytes = prep.tree.total_bytes();
    let public_dir = match &j.public_artifacts {
        Some(frozen) => {
            let x = r.fetch_tree(
                frozen,
                j.limits
                    .max_public_artifact_bytes
                    .clamp(1, MAX_BUNDLE_BYTES),
                "public",
            )?;
            if x.tree.digest() != prep.tree.digest() {
                bench.note("judge re-run of prepare produced a different public dir than the frozen one; the frozen one is used");
            }
            x.root
        }
        None => prep.public_dir.clone(),
    };
    let mut inputs = HashMap::new();
    for c in j
        .classes
        .iter()
        .flat_map(|c| c.batch.iter().chain(&c.fresh_batch))
    {
        if !inputs.contains_key(&c.id) {
            let req = r.fetch_file(&c.request, j.limits.max_request_bytes, "request")?;
            let wit = r.fetch_file(&c.witness, j.limits.max_witness_bytes, "witness")?;
            inputs.insert(c.id.clone(), (req, wit));
        }
    }
    let plan = SessionPlan {
        classes: j
            .classes
            .iter()
            .map(|c| ClassPlan {
                class_id: c.class_id.clone(),
                weight_ppm: c.weight_ppm,
                baseline_ns: c.baseline_ns,
            })
            .collect(),
        procedure: j.procedure.clone(),
        schedule_seed: j.schedule_seed,
        bootstrap_seed: j.bootstrap_seed,
        bootstrap_iterations: j.bootstrap_iterations,
        fresh_confirm_runs: if j.classes.iter().all(|c| !c.fresh_batch.is_empty()) {
            1
        } else {
            0
        },
    };
    let cpus = r.ctx.bench_cpus.clone();
    let mut runner = Runner {
        r,
        j,
        bundle,
        public_dir,
        inputs,
        cpus,
        failure: None,
    };
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
            let (gate, reason, detail) = failure.expect("candidate failure recorded");
            let mut g = Gate::start(gate);
            g.fail(reason, detail.clone());
            if gate == ObligationId::ResourceLimits {
                res = g;
                rel.fail(ReasonCode::ProverFailed, detail);
            } else if gate == ObligationId::ProverReliability {
                rel = g;
            } else if gate == ObligationId::Benchmark {
                bench = g;
            } else {
                out.gates.push(g.finish(GateStatus::Unknown, true));
            }
            bench.fail(ReasonCode::ProverFailed, "no score: a benchmark run failed");
            out.gates.push(bench.finish(GateStatus::Unknown, true));
            out.gates.push(res.finish(GateStatus::Unknown, true));
            out.gates.push(rel.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
        Err(e) => return Err(ExecError::Infra(e.to_string())),
    };
    if let Some(f) = session
        .flags
        .iter()
        .find(|f| f.starts_with("EXCESSIVE_OUTLIERS"))
    {
        return Err(ExecError::Infra(format!(
            "{f}: host too noisy, re-measure the session"
        )));
    }
    let score = match &session.score {
        Ok(s) => s.clone(),
        Err(e) => return Err(ExecError::Infra(format!("score: {}", e.code()))),
    };
    let classes: Vec<_> = session.classes.iter().map(|c| c.to_measurement()).collect();
    let result = BenchmarkResult {
        hardware_profile: j.hardware_profile.clone(),
        suite_revision: j.suite_revision.clone(),
        classes,
        score_milli: Some(score.score_milli),
        score_ci_milli: Some(score.half_width_milli),
        prepare_ns,
        public_artifact_bytes: public_bytes,
        measured_by: format!("arena-worker {}", r_worker_id(&runner)),
    };
    let report = serde_json::json!({
        "schedule_seed": session.schedule_seed,
        "schedule": session.schedule,
        "classes": session.classes,
        "bootstrap": score,
        "flags": session.flags,
    });
    let report_bytes = serde_json::to_vec(&report).map_err(|e| ExecError::Infra(e.to_string()))?;
    let d = runner.r.upload("benchmark_session", &report_bytes, true)?;
    bench.evidence("benchmark_session", d, true);
    if session
        .flags
        .iter()
        .any(|f| f.starts_with("CACHING_SUSPECTED"))
    {
        bench.note("CACHING_SUSPECTED: fresh-input batch markedly slower; re-run with fresh batches before ranking");
        bench.note(format!("score {} milli (unconfirmed)", score.score_milli));
        out.gates.push(bench.finish(GateStatus::Unknown, true));
    } else {
        bench.note(format!(
            "score {} ± {} milli (95% bootstrap, seed {})",
            score.score_milli, score.half_width_milli, score.seed
        ));
        out.gates.push(bench.finish(GateStatus::Pass, true));
    }
    res.note(format!(
        "prepare {} ms, public dir {} bytes; max proof {} bytes; max verify median {} ms",
        prepare_ns / 1_000_000,
        public_bytes,
        result
            .classes
            .iter()
            .map(|c| c.proof_bytes_max)
            .max()
            .unwrap_or(0),
        result
            .classes
            .iter()
            .map(|c| c.verify_median_ns)
            .max()
            .unwrap_or(0)
            / 1_000_000
    ));
    rel.note("every benchmark proof was claim-checked and accepted by verify");
    out.gates.push(res.finish(GateStatus::Pass, true));
    out.gates.push(rel.finish(GateStatus::Pass, true));
    out.benchmark = Some(result);
    Ok(out)
}

fn r_worker_id(runner: &Runner<'_, '_>) -> String {
    runner.r.ctx.worker_id.clone()
}
