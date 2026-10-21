//! Native final verifier V_d (ported from lane/pq-e2e-slice @ 480bf27f4, nv/e2e.rs): verifies
//! the FINAL proof under the final domain, checks the pinned level and the statement digest, and
//! checks the final proof's program columns against the pinned NV program
//! (`check_final_program`) - the check that makes the chain sound (without it a final proof of a
//! verify-nothing program exposing any statement is accepted).
use openvm_stark_backend::{
    keygen::types::MultiStarkVerifyingKey,
    proof::Proof,
    prover::{AirProvingContext, ProvingContext},
    FiatShamirTranscript, StarkEngine,
};
use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_matrix::dense::RowMajorMatrix;

use crate::sha384::config::{Digest, Sha384Config, Sha384CpuEngine, ShaTranscript, EF, F};

pub type SC = Sha384Config;

/// What V_d pins: the final vk (final domain), the NV program (its words) and the final level.
#[derive(Clone)]
pub struct VdSetup {
    pub vk_final: MultiStarkVerifyingKey<SC>,
    pub program: Vec<[u32; 4]>,
    pub level: u32,
}

fn eq_uni(l_skip: usize, x: EF, y: EF) -> EF {
    let (mut xp, mut yp) = (x, y);
    let mut res = EF::ONE;
    for _ in 0..l_skip {
        res = (xp + yp) * res + (xp - EF::ONE) * (yp - EF::ONE);
        xp = xp.square();
        yp = yp.square();
    }
    res * F::ONE.halve().exp_u64(l_skip as u64)
}

/// The final proof's batch point r and its NvAir openings, re-derived natively under the final
/// domain (the preamble of `verifier::verify`, then `verify_zerocheck_and_logup`).
fn final_point_and_openings(vk: &MultiStarkVerifyingKey<SC>, proof: &Proof<SC>) -> Result<(Vec<EF>, usize, Vec<(EF, EF)>), String> {
    use std::cmp::Reverse;
    let mvk = &vk.inner;
    let l_skip = mvk.params.l_skip;
    let num_airs = mvk.per_air.len();
    let mut t = ShaTranscript::new_layer(true);
    t.observe_commit(vk.pre_hash);
    t.observe_commit(proof.common_main_commit);
    for ((td, avk), pvs) in proof.trace_vdata.iter().zip(&mvk.per_air).zip(&proof.public_values) {
        if avk.preprocessed_data.is_some() || !avk.params.width.cached_mains.is_empty() {
            return Err("final vk has preprocessed/cached traces".into());
        }
        if !avk.is_required {
            t.observe(F::from_bool(td.is_some()));
        }
        let td = td.as_ref().ok_or("final proof: AIR absent")?;
        t.observe(F::from_usize(td.log_height));
        if let Some(h) = td.tight_height {
            t.observe(F::from_usize(h));
        }
        for &pv in pvs {
            t.observe(pv);
        }
    }
    let mut tid: Vec<usize> = (0..num_airs).collect();
    tid.sort_by_key(|&a| (Reverse(proof.trace_vdata[a].as_ref().unwrap().log_height), a));
    let n_per_trace: Vec<isize> = tid
        .iter()
        .map(|&a| proof.trace_vdata[a].as_ref().unwrap().log_height as isize - l_skip as isize)
        .collect();
    let omega_skip_pows: Vec<F> = F::two_adic_generator(l_skip).powers().take(1 << l_skip).collect();
    let r = openvm_stark_backend::verifier::batch_constraints::verify_zerocheck_and_logup::<SC, _>(
        &mut t,
        mvk,
        &proof.public_values,
        &proof.gkr_proof,
        &proof.batch_constraint_proof,
        &tid,
        &n_per_trace,
        &omega_skip_pows,
    )
    .map_err(|e| format!("zerocheck: {e:?}"))?;
    let ti = tid.iter().position(|&a| a == 0).unwrap();
    let mask = mvk.per_air[0].params.opening_masks()[0].clone();
    let open = openvm_stark_backend::proof::column_openings_by_mask(&proof.batch_constraint_proof.column_openings[ti][0], &mask);
    Ok((r, n_per_trace[ti] as usize, open))
}

/// The multilinear evaluation of the program words (P0..P3 combined by tau) at r, natively.
pub fn program_eval(program: &[[u32; 4]], r: &[EF], n: usize, l_skip: usize) -> EF {
    let tp = super::uair::tau_pows();
    let omega = F::two_adic_generator(l_skip);
    let lv: Vec<EF> = (0..1usize << l_skip).map(|i| eq_uni(l_skip, r[0], EF::from(omega.exp_u64(i as u64)))).collect();
    let mut eq = vec![EF::ONE];
    for &ri in &r[1..=n] {
        let mut next = Vec::with_capacity(2 * eq.len());
        next.extend(eq.iter().map(|&e| e * (EF::ONE - ri)));
        next.extend(eq.iter().map(|&e| e * ri));
        eq = next;
    }
    let mut acc = EF::ZERO;
    for (y, w) in program.iter().enumerate() {
        let p: EF = (0..4).map(|j| tp[j] * F::from_u32(w[j])).sum();
        acc += lv[y & ((1 << l_skip) - 1)] * eq[y >> l_skip] * p;
    }
    acc
}

/// Native check that the final proof's NvAir program columns open to the pinned program.
pub fn check_final_program(setup: &VdSetup, proof: &Proof<SC>) -> Result<(), String> {
    let (r, n, open) = final_point_and_openings(&setup.vk_final, proof)?;
    let l_skip = setup.vk_final.inner.params.l_skip;
    if setup.program.len() > 1usize << (l_skip + n) {
        return Err("program longer than the NvAir trace".into());
    }
    let tp = super::uair::tau_pows();
    let phat: EF = (0..4).map(|j| tp[j] * open[super::uair::U_P + j].0).sum();
    if phat != program_eval(&setup.program, &r, n, l_skip) {
        return Err("final program openings differ from the pinned program".into());
    }
    Ok(())
}

/// V_d: accept iff the final proof verifies under the pinned final vk (final domain), exposes
/// the pinned level, runs the pinned program (unless `skip_program`, the unsound variant kept
/// only to show the forgery), and exposes the statement digest of the claimed app public values.
///
/// This is the no-cached-pocket form; `verify_final_claim` is the general one and is what a
/// joined proof (TAPE, host-wire commitments) uses.
pub fn verify_final(setup: &VdSetup, engine_final: &Sha384CpuEngine, app_public_values: &[Vec<F>], proof: &Proof<SC>, skip_program: bool) -> Result<(), String> {
    verify_final_claim(setup, engine_final, &super::circuit::StatementClaim::new(app_public_values.to_vec()), proof, skip_program)
}

/// V_d with an explicit `StatementClaim`: besides the pinned vk, level and program, the final
/// proof must expose `claim.digest()`, i.e. SHA-384 over the claimed public values **and the
/// claimed cached roots** (P4: the base's TAPE root and the join's host-wire commitments).  The
/// chain only carries a root the base proof actually committed to, so this is what turns "the
/// base proof verified" into "the base proof verified *for this TAPE table*".
pub fn verify_final_claim(setup: &VdSetup, engine_final: &Sha384CpuEngine, claim: &super::circuit::StatementClaim, proof: &Proof<SC>, skip_program: bool) -> Result<(), String> {
    engine_final.verify(&setup.vk_final, proof).map_err(|e| format!("final proof: {e:?}"))?;
    let pvs = &proof.public_values[0];
    if pvs.len() != super::uair::NV_NUM_PVS {
        return Err("final public values".into());
    }
    if pvs[0] != F::from_u32(setup.level) {
        return Err(format!("level {} != pinned {}", pvs[0], setup.level));
    }
    check_height_caps(&setup.vk_final, proof)?;
    if !skip_program {
        check_final_program(setup, proof)?;
    }
    if !super::circuit::check_statement_claim(pvs, claim) {
        return Err("statement digest differs from the claim".into());
    }
    Ok(())
}

/// M4: every AIR's proof height respects the vk's per-AIR `maxLog`.  `engine.verify` already
/// rejects such a proof (`ProofShapeVDataError::LogHeightExceedsTableCap`), because the caps are
/// in the vk pre-hash V_d pins; this is the explicit form, used by the tests to show that the
/// *pinned vk* is what carries the cap.
pub fn check_height_caps(vk: &MultiStarkVerifyingKey<SC>, proof: &Proof<SC>) -> Result<(), String> {
    for (a, (avk, td)) in vk.inner.per_air.iter().zip(&proof.trace_vdata).enumerate() {
        if let (Some(cap), Some(td)) = (avk.params.max_log_trace_height, td) {
            if td.log_height > cap {
                return Err(format!("AIR {a}: log_height {} exceeds its maxLog {cap}", td.log_height));
            }
        }
    }
    Ok(())
}

/// The forger's program: verifies nothing, exposes `level` and the statement digest `d`.
pub fn forge_statement_program(level: u32, d: Digest) -> impl FnOnce(&mut super::builder::Builder) {
    move |b| {
        use super::builder::{digest_cells, ef_from, DigestCells};
        let l = b.c(F::from_u32(level));
        b.pv_level(l);
        let (lo, hi) = digest_cells(d);
        let lo = b.load(ef_from(lo));
        let hi = b.load(ef_from(hi));
        b.pv_digest(&DigestCells { lo, hi, digest: d });
    }
}

/// Prove pre-generated NV traces (AIR 0 carries the given public values).
pub fn prove_traces(
    circ: &super::circuit::NvCircuit,
    engine: &Sha384CpuEngine,
    mats: Vec<RowMajorMatrix<F>>,
    pvs: Vec<F>,
) -> (MultiStarkVerifyingKey<SC>, Proof<SC>) {
    use openvm_cpu_backend::CpuBackend;
    use openvm_stark_backend::prover::DeviceDataTransporter;
    let airs = circ.airs::<SC>();
    let (pk, vk) = engine.keygen(&airs);
    let ctxs: Vec<(usize, AirProvingContext<CpuBackend<SC>>)> = mats
        .into_iter()
        .enumerate()
        .map(|(i, m)| (i, if i == 0 { AirProvingContext::simple(m, pvs.clone()) } else { AirProvingContext::simple_no_pis(m) }))
        .collect();
    let d_pk = engine.device().transport_pk_to_device(&pk);
    let proof = engine.prove(&d_pk, ProvingContext::new(ctxs)).unwrap();
    engine.verify(&vk, &proof).unwrap();
    (vk, proof)
}

#[allow(dead_code)]
fn _unused(x: F) -> bool {
    Field::is_zero(&x)
}
