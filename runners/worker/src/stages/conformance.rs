//! `CONFORMANCE_DIFFERENTIAL`, `PROVER_RELIABILITY`, `RESOURCE_LIMITS`.
//!
//! Against the frozen build (bundle and judge-run `public_dir`, both bound by
//! TreeDigest): for every oracle case, `prove` in a sandbox holding the
//! witness; the claim bytes must equal the judge's expected claim
//! (`CLAIM_MISMATCH`); then `verify` in a separate sandbox receiving only the
//! public dir, claim and proof; it must accept. Fail-fast. Non-public case
//! ids never appear in summaries.

use super::common::{self, case_label, Verdict};
use crate::executor::{ExecError, JobRun, StageOut};
use crate::gate::Gate;
use crate::jobs::{ExecJob, RunLimits};
use arena_types::{GateStatus, ObligationId, ReasonCode};

pub fn run(r: &mut JobRun<'_>, j: &ExecJob) -> Result<StageOut, ExecError> {
    let mut conf = Gate::start(ObligationId::ConformanceDifferential);
    let mut rel = Gate::start(ObligationId::ProverReliability);
    let mut res = Gate::start(ObligationId::ResourceLimits);
    let mut out = StageOut {
        used_sandbox: true,
        ..Default::default()
    };
    let finish = |out: &mut StageOut, conf: Gate, rel: Gate, res: Gate, complete: bool| {
        let st = if complete {
            GateStatus::Pass
        } else {
            GateStatus::Unknown
        };
        out.gates.push(conf.finish(st, true));
        out.gates.push(rel.finish(st, true));
        out.gates.push(res.finish(st, true));
    };
    let limits = RunLimits::from_challenge(&j.challenge);
    // Fail closed (A06): pinned fixtures, per-class coverage, the committed
    // held-out set (when this worker holds held-out sets) and the version
    // pins of every case are checked before any candidate code runs.
    let suite = match common::suite(r, &j.challenge, &j.ctx, r.ctx.conformance_samples, true)? {
        Ok(s) => s,
        Err(m) => {
            conf.note(m);
            finish(&mut out, conf, rel, res, false);
            return Ok(out);
        }
    };
    let cases = &suite.cases;
    let bundle = common::fetch_bundle(r, &j.build, &j.manifest.entry)?;
    let public_dir = common::fetch_public(r, &j.build, &limits)?;
    let verifier = match common::verifier_for(r, j, &bundle, true)? {
        Ok(v) => v,
        Err(why) => {
            conf.note(why);
            finish(&mut out, conf, rel, res, false);
            return Ok(out);
        }
    };
    let env = common::EntryEnv {
        bundle: &bundle,
        entry: &j.manifest.entry,
        public_dir: &public_dir,
        limits: &limits,
        cpu_set: r.ctx.run_cpus.clone(),
        verifier: &verifier,
    };

    let mut max_proof = 0u64;
    let mut max_verify_ns = 0u64;
    let mut max_rss = 0u64;
    let mut passed = 0usize;
    for case in cases {
        let label = case_label(&case.id, case.public);
        let proved = match common::run_prove(r, &env, case)? {
            Ok(p) => p,
            Err(f) => {
                let note = format!("{label}: {}", f.detail_for(case.public));
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
        // RT-04: sizes on held-out cases are candidate-chosen and would be a
        // covert channel; only public cases feed the reported maxima.
        if case.public {
            max_proof = max_proof.max(proved.proof.len() as u64);
            max_rss = max_rss.max(proved.outcome.peak_rss_bytes);
        }
        if case.public {
            let d = r.upload(&format!("claim {}", case.id), &proved.claim, true)?;
            conf.evidence(format!("claim {}", case.id), d, true);
            let d = r.upload(&format!("proof {}", case.id), &proved.proof, true)?;
            rel.evidence(format!("proof {}", case.id), d, true);
        }
        let (v, vo) = common::run_verify(r, &env, &proved.claim_path, &proved.proof_path)?;
        if case.public {
            max_verify_ns = max_verify_ns.max(vo.wall_ns);
        }
        match v {
            Verdict::Accept => passed += 1,
            Verdict::Reject => {
                rel.fail(
                    ReasonCode::ProverFailed,
                    format!("{label}: verify rejected the honest proof"),
                );
                break;
            }
            Verdict::TimedOut => {
                res.fail(
                    ReasonCode::ResourceLimit,
                    format!(
                        "{label}: verify exceeded max_verify_ms {}",
                        limits.max_verify_ms
                    ),
                );
                rel.fail(
                    ReasonCode::ProverFailed,
                    format!("{label}: verify timed out on the honest proof"),
                );
                break;
            }
            Verdict::Error => {
                rel.fail(
                    ReasonCode::ProverFailed,
                    format!(
                        "{label}: verify errored on the honest proof ({})",
                        common::exit_for(&vo, case.public)
                    ),
                );
                break;
            }
            Verdict::BindingMismatch => {
                rel.fail(ReasonCode::ArtifactBindingFailed, "npai-verify: the verifier bytecode is not the certified image (digest mismatch)");
                break;
            }
        }
    }
    let n = cases.len();
    let complete = passed == n;
    if r.shadow != (0, 0) {
        conf.note(format!(
            "npai shadow (Lean reference): {} agreed, {} skipped (large/slow)",
            r.shadow.0, r.shadow.1
        ));
    }
    conf.note(format!(
        "{passed}/{n} cases conform ({} public fixtures, {} judge-sampled, {} held-out)",
        suite.public, suite.sampled, suite.heldout
    ));
    for note in &suite.notes {
        conf.note(note.clone());
    }
    rel.note(format!("{passed}/{n} honest proofs produced and accepted"));
    res.note(format!(
        "public cases: max proof {max_proof} bytes (cap {}), max verify {} ms (cap {}), peak memory {} MiB",
        limits.max_proof_bytes,
        max_verify_ns / 1_000_000,
        limits.max_verify_ms,
        max_rss >> 20
    ));
    finish(&mut out, conf, rel, res, complete);
    Ok(out)
}
