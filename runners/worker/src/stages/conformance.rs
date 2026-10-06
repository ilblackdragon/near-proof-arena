//! `CONFORMANCE_DIFFERENTIAL`, `PROVER_RELIABILITY`, `RESOURCE_LIMITS`.
//!
//! Against the frozen build (bundle and judge-run `public_dir`, both bound by
//! TreeDigest): for every oracle case, `prove` in a sandbox holding the
//! witness; the claim bytes must equal the judge's expected claim
//! (`CLAIM_MISMATCH`); then `verify` in a separate sandbox receiving only the
//! public dir, claim and proof; it must accept. Fail-fast. Non-public case
//! ids never appear in summaries.
//!
//! **Rejection cases** (oracles that provide them, v3): every judge-held
//! (claim, witness) pair that nearcore's own validator rejects or whose
//! chunk is outside the challenge's domain is handed to `prove` as well; if
//! it emits a proof, `verify` runs on the *requested* claim and that proof.
//! Acceptance fails CONFORMANCE_DIFFERENTIAL with `COUNTEREXAMPLE_FOUND`:
//! the candidate's acceptance disagrees with the reference validator.

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
    // Rejection cases: only after every positive case passed (fail-fast).
    let mut rej_note = None;
    if passed == n {
        let seeds = crate::executor::seeds(r.ctx, &j.ctx);
        let rej =
            match r
                .ctx
                .oracles
                .rejection_suite(&j.challenge, &seeds, r.ctx.conformance_samples)
            {
                Ok(x) => x,
                Err(crate::oracle::OracleError::Unavailable(m)) => {
                    conf.note(m);
                    finish(&mut out, conf, rel, res, false);
                    return Ok(out);
                }
                Err(e) => return Err(ExecError::Infra(e.to_string())),
            };
        if let Some(pin) = crate::jobs::RequestPin::from_challenge(&j.challenge) {
            for c in &rej.cases {
                pin.check_case(&c.request, None).map_err(|e| {
                    ExecError::Infra(format!(
                        "fail-closed: rejection case {} rejected: {e}",
                        case_label(&c.id, c.public)
                    ))
                })?;
            }
        }
        let (mut refused, mut rejected, mut accepted) = (0usize, 0usize, 0usize);
        for case in &rej.cases {
            let label = case_label(&case.id, case.public);
            let Some(proof) = common::run_prove_rejection(r, &env, case)? else {
                refused += 1;
                continue;
            };
            let claim = r.write_file(&case.request, "claim")?;
            let (v, _) = common::run_verify(r, &env, &claim, &proof)?;
            match v {
                Verdict::Accept => {
                    accepted += 1;
                    conf.fail(
                        ReasonCode::CounterexampleFound,
                        format!("{label}: verify accepted a proof of a claim the reference validator rejects (nearcore verdict / out of domain)"),
                    );
                    break;
                }
                Verdict::BindingMismatch => {
                    rel.fail(ReasonCode::ArtifactBindingFailed, "npai-verify: the verifier bytecode is not the certified image (digest mismatch)");
                    break;
                }
                _ => rejected += 1,
            }
        }
        if !rej.cases.is_empty() {
            rej_note = Some(format!(
                "{} rejection case(s) ({} public, {} judge-sampled, {} held-out; nearcore rejects or out of domain): {refused} refused by prove, {rejected} proofs rejected by verify, {accepted} accepted",
                rej.cases.len(), rej.public, rej.sampled, rej.heldout
            ));
        }
    }
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
    if let Some(m) = rej_note {
        conf.note(m);
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
