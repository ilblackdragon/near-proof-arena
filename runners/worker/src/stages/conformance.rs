//! `CONFORMANCE_DIFFERENTIAL`, `PROVER_RELIABILITY` and the
//! `RESOURCE_LIMITS` observations of conformance runs.
//!
//! 1. judge-run `prepare` → frozen `public_dir` (uploaded by digest);
//! 2. per oracle case: `prove` in a sandbox holding the witness; the claim
//!    bytes must equal the oracle's expected claim (`CLAIM_MISMATCH`);
//! 3. `verify` in a separate sandbox receiving only the public dir, claim
//!    and proof; it must accept the honest proof.
//!
//! Fail-fast: the first failing case stops the job. Held-out case ids never
//! appear in summaries.

use super::common::{self, case_label, Verdict};
use crate::executor::{ExecError, JobRun, StageOut};
use crate::gate::Gate;
use crate::jobs::ConformanceJob;
use arena_types::{GateStatus, ObligationId, ReasonCode};

pub fn run(r: &mut JobRun<'_>, j: &ConformanceJob) -> Result<StageOut, ExecError> {
    let mut conf = Gate::start(ObligationId::ConformanceDifferential);
    let mut rel = Gate::start(ObligationId::ProverReliability);
    let mut res = Gate::start(ObligationId::ResourceLimits);
    let mut out = StageOut { used_sandbox: true, ..Default::default() };
    let finish = |out: &mut StageOut, conf: Gate, rel: Gate, res: Gate, complete: bool| {
        let st = if complete { GateStatus::Pass } else { GateStatus::Unknown };
        out.gates.push(conf.finish(st, true));
        out.gates.push(rel.finish(st, true));
        out.gates.push(res.finish(st, true));
    };
    if j.cases.is_empty() {
        conf.note("no oracle cases supplied");
        finish(&mut out, conf, rel, res, false);
        return Ok(out);
    }
    let bundle = common::fetch_bundle(r, &j.bundle, &j.entry)?;
    let Some(prep) = common::run_prepare(r, &bundle, &j.entry, &j.params, &j.limits, &mut rel, &mut res)? else {
        conf.note("not run: prepare failed");
        finish(&mut out, conf, rel, res, false);
        return Ok(out);
    };
    let (_, public_tree) = r.upload_tree("public_artifacts", &prep.public_dir, &prep.tree, true)?;
    res.note(format!("prepare {} ms, public dir {} bytes", prep.outcome.wall_ns / 1_000_000, prep.tree.total_bytes()));
    res.evidence("public_artifacts_tree", public_tree, true);

    let env = common::EntryEnv { bundle: &bundle, entry: &j.entry, public_dir: &prep.public_dir, limits: &j.limits, cpu_set: None };
    let mut max_proof = 0u64;
    let mut max_verify_ns = 0u64;
    let mut passed = 0usize;
    for case in &j.cases {
        let label = case_label(&case.id, case.public);
        let req = r.fetch_file(&case.request, j.limits.max_request_bytes, "request")?;
        let wit = r.fetch_file(&case.witness, j.limits.max_witness_bytes, "witness")?;
        let proved = match common::run_prove(r, &env, &req, &wit, &case.expected_claim)? {
            Ok(p) => p,
            Err(f) => {
                let note = format!("{label}: {}", f.detail);
                match f.gate {
                    ObligationId::ConformanceDifferential => conf.fail(f.reason, note),
                    ObligationId::ResourceLimits => {
                        res.fail(f.reason, note.clone());
                        rel.fail(ReasonCode::ProverFailed, note);
                    }
                    _ => rel.fail(f.reason, note),
                }
                break;
            }
        };
        max_proof = max_proof.max(proved.proof.len() as u64);
        let claim_d = r.upload(&format!("claim:{}", case.id), &proved.claim, case.public)?;
        let proof_d = r.upload(&format!("proof:{}", case.id), &proved.proof, case.public)?;
        if case.public {
            conf.evidence(format!("claim:{}", case.id), claim_d, true);
            rel.evidence(format!("proof:{}", case.id), proof_d, true);
        }
        let (v, vo) = common::run_verify(r, &env, &proved.claim_path, &proved.proof_path)?;
        max_verify_ns = max_verify_ns.max(vo.wall_ns);
        match v {
            Verdict::Accept => passed += 1,
            Verdict::Reject => {
                rel.fail(ReasonCode::ProverFailed, format!("{label}: verify rejected the honest proof"));
                break;
            }
            Verdict::TimedOut => {
                res.fail(ReasonCode::ResourceLimit, format!("{label}: verify exceeded max_verify_ms {}", j.limits.max_verify_ms));
                rel.fail(ReasonCode::ProverFailed, format!("{label}: verify timed out on the honest proof"));
                break;
            }
            Verdict::Error => {
                rel.fail(ReasonCode::ProverFailed, format!("{label}: verify errored on the honest proof ({})", crate::executor::describe_exit(&vo)));
                break;
            }
        }
    }
    let n = j.cases.len();
    let complete = passed == n;
    let public = j.cases.iter().filter(|c| c.public).count();
    conf.note(format!("{passed}/{n} cases conform ({public} public, {} held-out)", n - public));
    rel.note(format!("{passed}/{n} honest proofs produced and accepted"));
    res.note(format!("max proof {max_proof} bytes, max verify {} ms", max_verify_ns / 1_000_000));
    finish(&mut out, conf, rel, res, complete);
    Ok(out)
}
