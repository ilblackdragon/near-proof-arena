//! `CONFORMANCE_DIFFERENTIAL`, `PROVER_RELIABILITY`, `RESOURCE_LIMITS`.
//!
//! Against the frozen build (bundle and judge-run `public_dir`, both bound by
//! TreeDigest): for every oracle case, `prove` in a sandbox holding the
//! witness; the claim bytes must equal the judge's expected claim
//! (`CLAIM_MISMATCH`); then `verify` in a separate sandbox receiving only the
//! public dir, claim and proof; it must accept. Fail-fast. Non-public case
//! ids never appear in summaries.

use super::common::{self, case_label, Verdict};
use crate::executor::{seed_parts, ExecError, JobRun, StageOut};
use crate::gate::Gate;
use crate::jobs::{ExecJob, RunLimits};
use crate::oracle::OracleError;
use arena_types::{GateStatus, ObligationId, ReasonCode};

pub fn run(r: &mut JobRun<'_>, j: &ExecJob) -> Result<StageOut, ExecError> {
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
    if let Some(why) = common::unsupported_verify_route(&j.manifest.entry) {
        conf.note(why);
        finish(&mut out, conf, rel, res, false);
        return Ok(out);
    }
    let limits = RunLimits::from_challenge(&j.challenge);
    let parts = seed_parts(&j.ctx);
    let parts: Vec<&str> = parts.iter().map(|s| s.as_str()).collect();
    let cases = match r.ctx.oracles.get(&j.challenge).and_then(|o| {
        let fx = r.ctx.oracles.fixtures_for(&j.challenge)?;
        o.conformance_cases(&j.challenge, fx.as_deref(), &parts, r.ctx.conformance_samples)
    }) {
        Ok(c) if !c.is_empty() => c,
        Ok(_) => {
            conf.note("oracle produced no cases");
            finish(&mut out, conf, rel, res, false);
            return Ok(out);
        }
        Err(OracleError::Unavailable(m)) => {
            conf.note(m);
            finish(&mut out, conf, rel, res, false);
            return Ok(out);
        }
        Err(e @ OracleError::Broken(_)) => return Err(ExecError::Infra(e.to_string())),
    };
    let bundle = common::fetch_bundle(r, &j.build, &j.manifest.entry)?;
    let public_dir = common::fetch_public(r, &j.build, &limits)?;
    let env = common::EntryEnv { bundle: &bundle, entry: &j.manifest.entry, public_dir: &public_dir, limits: &limits, cpu_set: None };

    let mut max_proof = 0u64;
    let mut max_verify_ns = 0u64;
    let mut max_rss = 0u64;
    let mut passed = 0usize;
    for case in &cases {
        let label = case_label(&case.id, case.public);
        let proved = match common::run_prove(r, &env, case)? {
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
        max_rss = max_rss.max(proved.outcome.peak_rss_bytes);
        if case.public {
            let d = r.upload(&format!("claim {}", case.id), &proved.claim, true)?;
            conf.evidence(format!("claim {}", case.id), d, true);
            let d = r.upload(&format!("proof {}", case.id), &proved.proof, true)?;
            rel.evidence(format!("proof {}", case.id), d, true);
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
                res.fail(ReasonCode::ResourceLimit, format!("{label}: verify exceeded max_verify_ms {}", limits.max_verify_ms));
                rel.fail(ReasonCode::ProverFailed, format!("{label}: verify timed out on the honest proof"));
                break;
            }
            Verdict::Error => {
                rel.fail(ReasonCode::ProverFailed, format!("{label}: verify errored on the honest proof ({})", crate::executor::describe_exit(&vo)));
                break;
            }
        }
    }
    let n = cases.len();
    let complete = passed == n;
    let public = cases.iter().filter(|c| c.public).count();
    conf.note(format!("{passed}/{n} cases conform ({public} public fixtures, {} judge-sampled)", n - public));
    rel.note(format!("{passed}/{n} honest proofs produced and accepted"));
    res.note(format!(
        "max proof {max_proof} bytes (cap {}), max verify {} ms (cap {}), peak memory {} MiB",
        limits.max_proof_bytes,
        max_verify_ns / 1_000_000,
        limits.max_verify_ms,
        max_rss >> 20
    ));
    finish(&mut out, conf, rel, res, complete);
    Ok(out)
}
