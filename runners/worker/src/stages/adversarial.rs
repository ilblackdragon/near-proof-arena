//! `ADVERSARIAL_PROOFS`: every hostile (claim, proof) pair produced by the
//! selected mutators must not be accepted by `verify`. Honest controls run
//! first: a verifier that now rejects an honest proof it accepted during
//! conformance is nondeterministic (and would make this gate vacuous).

use super::common::{self, Verdict};
use crate::executor::{ExecError, JobRun, StageOut, MAX_BUNDLE_BYTES};
use crate::gate::Gate;
use crate::jobs::AdversarialJob;
use crate::mutators::{HonestPair, MutationCtx};
use arena_types::{GateStatus, ObligationId, ReasonCode};

/// `mutator/variant` without case ids (which may be held-out).
fn public_label(l: &str) -> String {
    l.split('/').take(2).collect::<Vec<_>>().join("/")
}

pub fn run(r: &mut JobRun<'_>, j: &AdversarialJob) -> Result<StageOut, ExecError> {
    let mut g = Gate::start(ObligationId::AdversarialProofs);
    let mut out = StageOut { used_sandbox: true, ..Default::default() };
    if j.honest.is_empty() {
        g.note("no honest proofs supplied: cannot derive hostile inputs");
        out.gates.push(g.finish(GateStatus::Unknown, true));
        return Ok(out);
    }
    let bundle = common::fetch_bundle(r, &j.bundle, &j.entry)?;
    let public = r.fetch_tree(&j.public_artifacts, j.limits.max_public_artifact_bytes.clamp(1, MAX_BUNDLE_BYTES), "public")?;
    let mut honest = vec![];
    for h in &j.honest {
        honest.push(HonestPair {
            case_id: h.case_id.clone(),
            claim: r.fetch(&h.claim, j.limits.max_claim_bytes)?,
            proof: r.fetch(&h.proof, j.limits.max_proof_bytes)?,
        });
    }
    let env = common::EntryEnv { bundle: &bundle, entry: &j.entry, public_dir: &public.root, limits: &j.limits, cpu_set: None };
    // Honest controls.
    for (i, h) in honest.iter().enumerate() {
        let (c, p) = write_pair(r, &h.claim, &h.proof)?;
        let (v, o) = common::run_verify(r, &env, &c, &p)?;
        if v != Verdict::Accept {
            g.fail(
                ReasonCode::VerifierNondeterministic,
                format!("honest control #{i} not accepted ({}); verifier is nondeterministic or environment-dependent", crate::executor::describe_exit(&o)),
            );
            out.gates.push(g.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
    }
    let ctx = MutationCtx { honest: &honest, max_proof_bytes: j.limits.max_proof_bytes };
    let hostile = match r.ctx.mutators.generate(&j.mutators, &ctx, j.seed) {
        Ok(h) => h,
        Err(e) => return Err(ExecError::Infra(format!("mutators: {e}"))),
    };
    let (mut rejected, mut errored, mut timeouts) = (0usize, 0usize, 0usize);
    let mut accepted: Vec<String> = vec![];
    for h in &hostile {
        let (c, p) = write_pair(r, &h.claim, &h.proof)?;
        let (v, _) = common::run_verify(r, &env, &c, &p)?;
        match v {
            Verdict::Accept => accepted.push(public_label(&h.label)),
            Verdict::Reject => rejected += 1,
            Verdict::Error => errored += 1,
            Verdict::TimedOut => timeouts += 1,
        }
    }
    let n = hostile.len();
    if n == 0 {
        g.note("mutators produced no hostile inputs");
        out.gates.push(g.finish(GateStatus::Unknown, true));
        return Ok(out);
    }
    if !accepted.is_empty() {
        accepted.sort();
        accepted.dedup();
        g.fail(ReasonCode::HostileProofAccepted, format!("verify accepted hostile proofs: {}", accepted.join(", ")));
    }
    g.note(format!(
        "{n} hostile inputs from [{}]: {rejected} rejected, {errored} errored (not accepted), {timeouts} timed out (not accepted), {} accepted",
        if j.mutators.is_empty() { r.ctx.mutators.names().join(",") } else { j.mutators.join(",") },
        n - rejected - errored - timeouts
    ));
    out.gates.push(g.finish(GateStatus::Pass, true));
    Ok(out)
}

fn write_pair(r: &mut JobRun<'_>, claim: &[u8], proof: &[u8]) -> Result<(std::path::PathBuf, std::path::PathBuf), ExecError> {
    let d = r.fresh("pair");
    std::fs::create_dir(&d)?;
    let (c, p) = (d.join("claim.bin"), d.join("proof.bin"));
    std::fs::write(&c, claim)?;
    std::fs::write(&p, proof)?;
    Ok((c, p))
}
