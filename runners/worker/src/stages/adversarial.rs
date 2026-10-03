//! `ADVERSARIAL_PROOFS`: every hostile (claim, proof) pair produced by the
//! selected mutators must not be accepted by `verify`. Honest controls run
//! first: a verifier that now rejects an honest proof it accepted during
//! conformance is nondeterministic (and would make this gate vacuous).

use super::common::{self, Verdict};
use crate::executor::{seed_parts, ExecError, JobRun, StageOut};
use crate::gate::Gate;
use crate::jobs::{ExecJob, RunLimits};
use crate::mutators::{HonestPair, MutationCtx};
use crate::oracle::OracleError;
use arena_types::{GateStatus, ObligationId, ReasonCode};

/// Honest proofs the hostile inputs are derived from.
const HONEST_CASES: usize = 3;
/// Upper bound on hostile inputs per job (deterministic subsample beyond).
const MAX_HOSTILE: usize = 240;

/// `mutator/variant` without case ids (which may be held-out).
fn public_label(l: &str) -> String {
    l.split('/').take(2).collect::<Vec<_>>().join("/")
}

pub fn run(r: &mut JobRun<'_>, j: &ExecJob) -> Result<StageOut, ExecError> {
    let mut g = Gate::start(ObligationId::AdversarialProofs);
    let mut out = StageOut { used_sandbox: true, ..Default::default() };
    if let Some(why) = common::unsupported_verify_route(&j.manifest.entry) {
        g.note(why);
        out.gates.push(g.finish(GateStatus::Unknown, true));
        return Ok(out);
    }
    let limits = RunLimits::from_challenge(&j.challenge);
    let parts_owned = seed_parts(&j.ctx);
    let parts: Vec<&str> = parts_owned.iter().map(|s| s.as_str()).collect();
    let mut cases = match r.ctx.oracles.get(&j.challenge).and_then(|o| {
        let fx = r.ctx.oracles.fixtures_for(&j.challenge)?;
        o.conformance_cases(&j.challenge, fx.as_deref(), &parts, HONEST_CASES)
    }) {
        Ok(c) => c,
        Err(OracleError::Unavailable(m)) => {
            g.note(m);
            out.gates.push(g.finish(GateStatus::Unknown, true));
            return Ok(out);
        }
        Err(e) => return Err(ExecError::Infra(e.to_string())),
    };
    // Prefer distinct claims (swap mutators need two different claims).
    cases.sort_by_key(|c| !c.public);
    let mut picked: Vec<crate::oracle::Case> = vec![];
    for c in cases {
        if picked.len() < HONEST_CASES && !picked.iter().any(|p| p.expected_claim == c.expected_claim) {
            picked.push(c);
        }
    }
    let bundle = common::fetch_bundle(r, &j.build, &j.manifest.entry)?;
    let public_dir = common::fetch_public(r, &j.build, &limits)?;
    let env = common::EntryEnv { bundle: &bundle, entry: &j.manifest.entry, public_dir: &public_dir, limits: &limits, cpu_set: None };
    let mut honest = vec![];
    for case in &picked {
        match common::run_prove(r, &env, case)? {
            Ok(p) => honest.push(HonestPair { case_id: case.id.clone(), claim: p.claim, proof: p.proof }),
            Err(f) => {
                g.note(format!("could not obtain an honest proof ({}); see the conformance gates", f.detail));
                out.gates.push(g.finish(GateStatus::Unknown, true));
                return Ok(out);
            }
        }
    }
    // Honest controls, each verified twice: rejected outright = the
    // conformance gates fail; accepted then rejected = nondeterminism.
    for (i, h) in honest.iter().enumerate() {
        let (c, p) = write_pair(r, &h.claim, &h.proof)?;
        for round in 0..2 {
            let (v, o) = common::run_verify(r, &env, &c, &p)?;
            if v != Verdict::Accept {
                if round == 0 {
                    g.note(format!("verify does not accept honest proof #{i} ({}); hostile inputs are meaningless (see conformance)", crate::executor::describe_exit(&o)));
                    out.gates.push(g.finish(GateStatus::Unknown, true));
                } else {
                    g.fail(ReasonCode::VerifierNondeterministic, format!("verify accepted honest proof #{i} once, then not ({})", crate::executor::describe_exit(&o)));
                    out.gates.push(g.finish(GateStatus::Unknown, true));
                }
                return Ok(out);
            }
        }
    }
    let seed = arena_measure::stats::derive_seed("adversarial", &parts).map_err(ExecError::Infra)?;
    let ctx = MutationCtx { honest: &honest, max_proof_bytes: limits.max_proof_bytes };
    let mut hostile = match r.ctx.mutators.generate(&[], &ctx, seed) {
        Ok(h) => h,
        Err(e) => return Err(ExecError::Infra(format!("mutators: {e}"))),
    };
    let generated = hostile.len();
    if hostile.len() > MAX_HOSTILE {
        // Deterministic stride subsample: every mutator family stays represented.
        let step = hostile.len() as f64 / MAX_HOSTILE as f64;
        hostile = (0..MAX_HOSTILE).map(|i| hostile[(i as f64 * step) as usize].clone()).collect();
    }
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
    if generated > n {
        g.note(format!("{generated} hostile inputs generated, {n} run (deterministic subsample)"));
    }
    g.note(format!(
        "{n} hostile inputs from [{}]: {rejected} rejected, {errored} errored (not accepted), {timeouts} timed out (not accepted), {} accepted",
        r.ctx.mutators.names().join(","),
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
