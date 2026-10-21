//! The SWIRL verifier (stark-backend `verifier/*`) as an NV program.  Mirrors the native
//! code step by step; every data-dependent choice (query indices, Merkle directions) goes
//! through BIT rows, so the instruction stream depends only on the child vk, the params
//! and the (fixed) child trace heights.
use core::cmp::Reverse;

use itertools::Itertools;
use openvm_stark_backend::{
    calculate_n_logup,
    hasher::MerkleHasher,
    keygen::types::MultiStarkVerifyingKey,
    proof::Proof,
    verifier::proof_shape::verify_proof_shape,
    air_builders::symbolic::{symbolic_variable::Entry, SymbolicExpressionNode},
};
use p3_field::{
    batch_multiplicative_inverse, BasedVectorSpace, Field, PrimeCharacteristicRing,
    PrimeField32, TwoAdicField,
};

use super::builder::{coeffs, ef_from, Builder, DigestCells, V};
use super::fmt::limbs_digest;
use crate::sha384::config::{Sha384Config, ShaHasher, EF, F};

type SC = Sha384Config;

// ---------------------------------------------------------------------------------------
// test-only cheating-witness hooks (NV-faithful audit, faithful_tr_tests.rs)
// ---------------------------------------------------------------------------------------

/// A cheating witness choice applied once (first applicable query) by the program generator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tamper {
    None,
    /// query index bits of x + p (when x + p < 2^31) instead of x
    NonCanonicalIndex,
    /// flip index bit 0 (recomposition must fail)
    IndexBitFlip,
    /// Merkle path level 0: current digest placed on the wrong side
    MerkleSwapLr,
    /// initial round, query 0: the opened rows of query 1 at query 0's index
    OtherLeaf,
    /// x15: x >> m = 15 (q - 1) + 15 instead of 15 q + 0
    X15AEquals15,
    /// PoW: the low-limb Load cell absorbs the top bits of limbs 1, 2 (bug B3 demo)
    PowFreeLimb,
}
#[cfg(test)]
thread_local! {
    static TAMPER: core::cell::Cell<Tamper> = const { core::cell::Cell::new(Tamper::None) };
    static TAMPER_HIT: core::cell::Cell<bool> = const { core::cell::Cell::new(false) };
}
#[cfg(test)]
pub fn set_tamper(t: Tamper) {
    TAMPER.with(|c| c.set(t));
    TAMPER_HIT.with(|c| c.set(false));
}
#[cfg(test)]
pub fn tamper_hit() -> bool {
    TAMPER_HIT.with(|c| c.get())
}
/// True (once) if tamper `t` is active and not yet applied; marks it applied.
#[cfg(test)]
pub(crate) fn tamper_now(t: Tamper) -> bool {
    let on = TAMPER.with(|c| c.get()) == t && !TAMPER_HIT.with(|c| c.get());
    if on {
        TAMPER_HIT.with(|c| c.set(true));
    }
    on
}
#[cfg(not(test))]
#[inline(always)]
pub(crate) fn tamper_now(_: Tamper) -> bool {
    false
}
/// Peek without consuming.
#[cfg(test)]
pub(crate) fn tamper_active(t: Tamper) -> bool {
    TAMPER.with(|c| c.get()) == t && !TAMPER_HIT.with(|c| c.get())
}
#[cfg(not(test))]
#[inline(always)]
pub(crate) fn tamper_active(_: Tamper) -> bool {
    false
}

/// Shape facts the program depends on (asserted, not computed from the proof).
#[derive(Clone, Debug)]
pub struct NvShape {
    pub log_heights: Vec<usize>,
}

impl NvShape {
    pub fn of(proof: &Proof<SC>) -> Self {
        Self {
            log_heights: proof
                .trace_vdata
                .iter()
                .map(|v| v.as_ref().expect("NV requires every AIR present").log_height)
                .collect(),
        }
    }
}

// ---------------------------------------------------------------------------------------
// small helpers on the builder
// ---------------------------------------------------------------------------------------

fn sum(b: &mut Builder, xs: &[V]) -> V {
    let mut acc = b.c(F::ZERO);
    for &x in xs {
        acc = b.add(acc, x);
    }
    acc
}

/// 1 - x - y + 2xy
/// Witness inverse of a (non-zero) Ext12 cell, checked: x * inv == 1.
fn inv_checked(b: &mut Builder, x: V, what: &str) -> V {
    let iv = if x.val == EF::ZERO { EF::ZERO } else { x.val.inverse() };
    let i = b.load(iv);
    let p = b.mul(x, i);
    let one = b.c(F::ONE);
    b.assert_eq(p, one, what);
    i
}

fn eq1(b: &mut Builder, x: V, y: V) -> V {
    let xy = b.mul(x, y);
    let s = b.add(x, y);
    let z = b_zero(b);
    let t = b.dbl_add(xy, z);
    let one = b.c(F::ONE);
    let u = b.sub(one, s);
    b.add(u, t)
}
fn b_zero(b: &mut Builder) -> V {
    b.c(F::ZERO)
}

fn eq_mle(b: &mut Builder, x: &[V], y: &[V]) -> V {
    let mut acc = b.c(F::ONE);
    for (&xi, &yi) in x.iter().zip(y) {
        let e = eq1(b, xi, yi);
        acc = b.mul(acc, e);
    }
    acc
}

/// eq(x, bits) for constant bits: prod (bit ? x : 1 - x)
fn eq_mle_bits(b: &mut Builder, x: &[V], bits: &[bool]) -> V {
    let mut acc = b.c(F::ONE);
    for (&xi, &bit) in x.iter().zip(bits) {
        let f = if bit { xi } else { b.one_minus(xi) };
        acc = b.mul(acc, f);
    }
    acc
}

fn exp_pow2(b: &mut Builder, x: V, k: usize) -> V {
    let mut y = x;
    for _ in 0..k {
        y = b.square(y);
    }
    y
}

fn powers_of_2(b: &mut Builder, x: V, n: usize) -> Vec<V> {
    let mut out = Vec::with_capacity(n);
    let mut y = x;
    for i in 0..n {
        out.push(y);
        if i + 1 < n {
            y = b.square(y);
        }
    }
    out
}

/// eval_eq_uni(l_skip, x, y)
fn eq_uni(b: &mut Builder, l_skip: usize, x: V, y: V) -> V {
    let xs = powers_of_2(b, x, l_skip);
    let ys = powers_of_2(b, y, l_skip);
    let one = b.c(F::ONE);
    let mut res = one;
    for i in 0..l_skip {
        let s = b.add(xs[i], ys[i]);
        let t = b.mul(s, res);
        let xm = b.sub(xs[i], one);
        let ym = b.sub(ys[i], one);
        let u = b.mul(xm, ym);
        res = b.add(t, u);
    }
    b.mul_c(res, F::ONE.halve().exp_u64(l_skip as u64))
}

/// eval_eq_uni_at_one
fn eq_uni_at_one(b: &mut Builder, l_skip: usize, x: V) -> V {
    let xs = powers_of_2(b, x, l_skip);
    let mut res = b.c(F::ONE);
    for xp in xs {
        let t = b.add_c(xp, F::ONE);
        res = b.mul(res, t);
    }
    b.mul_c(res, F::ONE.halve().exp_u64(l_skip as u64))
}

fn horner(b: &mut Builder, coeffs: &[V], x: V) -> V {
    let mut acc = b.c(F::ZERO);
    for &c in coeffs.iter().rev() {
        let t = b.mul(acc, x);
        acc = b.add(t, c);
    }
    acc
}

fn interp_linear(b: &mut Builder, e0: V, e1: V, x: V) -> V {
    let p = b.sub(e1, e0);
    let t = b.mul(p, x);
    b.add(t, e0)
}

fn interp_quadratic(b: &mut Builder, e: [V; 3], x: V) -> V {
    let s1 = b.sub(e[1], e[0]);
    let s2 = b.sub(e[2], e[1]);
    let d = b.sub(s2, s1);
    let p = b.mul_c(d, F::ONE.halve());
    let q = b.sub(s1, p);
    let t = b.mul(p, x);
    let t = b.add(t, q);
    let t = b.mul(t, x);
    b.add(t, e[0])
}

fn interp_cubic(b: &mut Builder, e: [V; 4], x: V) -> V {
    let inv6 = F::from_u64(6).inverse();
    let s1 = b.sub(e[1], e[0]);
    let s2 = b.sub(e[2], e[0]);
    let s3 = b.sub(e[3], e[0]);
    let s21 = b.sub(s2, s1);
    let s21x3 = b.mul_c(s21, F::from_u64(3));
    let d3 = b.sub(s3, s21x3);
    let p = b.mul_c(d3, inv6);
    let sd = b.sub(s2, d3);
    let sdh = b.mul_c(sd, F::ONE.halve());
    let q = b.sub(sdh, s1);
    let r = b.sub(s1, p);
    let r = b.sub(r, q);
    let t = b.mul(p, x);
    let t = b.add(t, q);
    let t = b.mul(t, x);
    let t = b.add(t, r);
    let t = b.mul(t, x);
    b.add(t, e[0])
}

/// Index bits of a sampled base element: all 31 bits are BIT rows (with the canonical
/// check value <= p - 1); returns the low `nbits` bits (LSB first).
fn decompose_index(b: &mut Builder, s: V, nbits: usize, qid: u32) -> Vec<V> {
    let mut x = coeffs(s.val)[0].as_canonical_u32() as u64;
    if (x + crate::sha384::config::BABYBEAR_P) < (1 << 31) && tamper_now(Tamper::NonCanonicalIndex) {
        x += crate::sha384::config::BABYBEAR_P;
    }
    let flip = tamper_now(Tamper::IndexBitFlip) as u64;
    let bits: Vec<V> = (0..31)
        .map(|j| {
            let _ = qid;
            b.load_bit(((x >> j) & 1 ^ if j == 0 { flip } else { 0 }) == 1)
        })
        .collect();
    // recompose (MSB first): acc = 2 acc + bit
    let mut acc = b.c(F::ZERO);
    for j in (0..31).rev() {
        acc = b.dbl_add(acc, bits[j]);
    }
    b.assert_eq(acc, s, "index recomposition");
    // canonical: value <= 15 * 2^27 = p - 1: bits 27..30 all one => bits 0..26 zero.
    let mut top = bits[27];
    for j in 28..31 {
        top = b.mul(top, bits[j]);
    }
    let mut low = b.c(F::ZERO);
    for j in (0..27).rev() {
        low = b.dbl_add(low, bits[j]);
    }
    let t = b.mul(top, low);
    b.zero(t, "index canonical");
    bits[..nbits].to_vec()
}

/// omega^idx for idx = sum bits[j] 2^j (bits LSB first), omega of order 2^log_dom.
/// x15 query index (odd factor 15): the sample x (all 31 bits as BIT rows, canonical, and
/// x != p - 1, i.e. the top-4 AND is zero) is reduced mod 15 * 2^m: u0 = low m bits,
/// x >> m = 15 q + a with a in [0, 15) and q < 2^(27 - m) (witness bits).  Returns
/// (index bits = u0 bits ++ a bits, a bits).
fn decompose_index_x15(b: &mut Builder, s: V, m: usize, qid: u32) -> (Vec<V>, Vec<V>) {
    // x = low + 2^m (15 q + a) with low < 2^m, a < 15 and q < 2^(27 - m) (bits): the unique
    // representation of x < 15 * 2^27 = p - 1 (x = p - 1 has none and is rejected, as the native
    // sampler re-samples it); 2 rows per low / q bit instead of recomposing all 31 bits
    let _ = qid;
    let x = coeffs(s.val)[0].as_canonical_u32();
    if x as u64 >= 15u64 << 27 {
        b.failures.push("x15 index: x = p - 1".into());
    }
    let low: Vec<V> = (0..m).map(|j| b.load_bit((x >> j) & 1 == 1)).collect();
    let mut lowv = b.c(F::ZERO);
    for j in (0..m).rev() {
        lowv = b.dbl_add(lowv, low[j]);
    }
    let y = x >> m;
    let (mut q, mut a) = (y / 15, y % 15);
    if a == 0 && q >= 1 && tamper_now(Tamper::X15AEquals15) {
        q -= 1;
        a = 15;
    }
    let abits: Vec<V> = (0..4).map(|j| b.load_bit((a >> j) & 1 == 1)).collect();
    let mut a_and = abits[0];
    for &bb in &abits[1..] {
        a_and = b.mul(a_and, bb);
    }
    b.zero(a_and, "x15 index: a = 15 rejected");
    let qn = 27 - m;
    let mut qv = b.c(F::ZERO);
    for j in (0..qn).rev() {
        let bc = b.load_bit((q >> j) & 1 == 1);
        qv = b.dbl_add(qv, bc);
    }
    let mut av = b.c(F::ZERO);
    for j in (0..4).rev() {
        av = b.dbl_add(av, abits[j]);
    }
    let q15 = b.mul_c(qv, F::from_u32(15));
    let yv = b.add(q15, av);
    let hi = b.mul_c(yv, F::from_u32(1 << m));
    let xr = b.add(hi, lowv);
    b.assert_eq(xr, s, "x15 index: x = low + 2^m (15 q + a)");
    let mut idx = low;
    idx.extend(abits.iter().copied());
    (idx, abits)
}

/// Per-query Merkle paths from a canonical multiproof (levers spec): `leaves` are
/// (index, leaf digest) in query order; returns each query's siblings bottom-up.
fn decompress_multiproof(leaves: &[(usize, crate::sha384::config::Digest)], stream: &[crate::sha384::config::Digest], depth: usize, failures: &mut Vec<String>) -> Vec<Vec<crate::sha384::config::Digest>> {
    use std::collections::BTreeMap;
    let mut levels: Vec<BTreeMap<usize, crate::sha384::config::Digest>> = vec![BTreeMap::new(); depth + 1];
    for &(i, d) in leaves {
        levels[0].insert(i, d);
    }
    let mut it = stream.iter();
    for l in 0..depth {
        let known: Vec<usize> = levels[l].keys().copied().collect();
        let mut i = 0;
        while i < known.len() {
            let idx = known[i];
            let pair = idx ^ 1;
            if !(i + 1 < known.len() && known[i + 1] == pair) {
                let sib = match it.next() {
                    Some(d) => *d,
                    None => {
                        failures.push("multiproof stream too short".into());
                        [0u64; 6]
                    }
                };
                levels[l].insert(pair, sib);
                i += 1;
            } else {
                i += 2;
            }
            let (lft, rgt) = (levels[l][&(idx & !1)], levels[l][&(idx | 1)]);
            levels[l + 1].insert(idx >> 1, ShaHasher.compress(lft, rgt));
        }
    }
    if it.next().is_some() {
        failures.push("multiproof stream too long".into());
    }
    leaves
        .iter()
        .map(|&(i, _)| (0..depth).map(|l| levels[l][&((i >> l) ^ 1)]).collect())
        .collect()
}

fn pow_by_bits(b: &mut Builder, omega: F, bits: &[V]) -> V {
    let mut acc = b.c(F::ONE);
    let mut w = omega;
    for &bit in bits {
        let k = b.c(w - F::ONE);
        let t = b.mul(bit, k);
        acc = b.mul_add_a(acc, t);
        w = w.square();
    }
    acc
}

/// check_witness(bits, w): observe w, sample, low `bits` bits of the sample are zero.
/// Bit keys use ids >= POW_KEY_BASE (never looked up by the Merkle AIR).
pub const POW_KEY_BASE: u32 = 1 << 20;
fn pow_check(b: &mut Builder, bits: usize, witness: F, id: &mut u32) {
    let _ = (POW_KEY_BASE, &id);
    b.pow(bits, &[witness]);
}

// ---------------------------------------------------------------------------------------
// the verifier
// ---------------------------------------------------------------------------------------

pub struct NvChildData {
    /// commit ids: 0 = common main; then, per trace in sorted order, its preprocessed commit
    /// (a vk constant) and its cached commits (proof witnesses); WHIR round r codeword commit = r.
    pub num_stacking_commits: usize,
}

/// Build the verifier program for `proof` under `vk`.  Requirements (asserted): every
/// AIR present, trace heights >= 2^l_skip.  Preprocessed traces (pq-nv-preprocessed): the
/// commitment is a constant of the program (from the child vk, which the vk pre-hash binds);
/// cached traces: the commitment is a witness observed in the preamble.  Each is one more
/// stacked commitment, opened in WHIR round 0 at the shared query points.
///
/// [agg] Returns the child's public-value cells (per AIR), observed in its transcript, so an
/// aggregation node can read several children's statements.
pub fn build_verifier(b: &mut Builder, vk: &MultiStarkVerifyingKey<SC>, proof: &Proof<SC>) -> Vec<Vec<V>> {
    let mvk = &vk.inner;
    let params = &mvk.params;
    let l_skip = params.l_skip;
    // O-2: the child's query counts are its vk's agreement table (canonical for its schedule);
    // the table is part of the child vk (pre-hash), a constant of this program
    if !params.whir.check_agreement(params.log_blowup, l_skip + params.n_stack) {
        b.failures.push("child WHIR agreement table".into());
    }
    let num_airs = mvk.per_air.len();
    for (a, (avk, td)) in mvk.per_air.iter().zip(&proof.trace_vdata).enumerate() {
        let td = td.as_ref().expect("all AIRs present");
        assert!(td.log_height >= l_skip, "short traces not supported yet");
        // preprocessed: the height is fixed by the vk (native PreprocessedTraceHeightMismatch);
        // heights are program constants, so this is static
        if let Some(pd) = &avk.preprocessed_data {
            assert_eq!(pd.hypercube_dim + l_skip as isize, td.log_height as isize, "preprocessed trace height != vk");
        }
        // M4 (per-table height cap): `log_height <= maxLog_t`, a vk constant (the ported
        // classical table's `maxLog`).  The height is a program constant too, so the check is
        // static exactly like the LogUp count check below (B2) and costs no rows.  The native
        // verifier rejects the same proof in `verify_proof_shape`
        // (`ProofShapeVDataError::LogHeightExceedsTableCap`); this stops program generation, so
        // no level is ever proved for a child whose table outgrew its soundness bound.
        if let Some(max_log) = avk.params.max_log_trace_height.filter(|&m| td.log_height > m) {
            let msg = format!("AIR {a}: log_height {} exceeds its maxLog {max_log}", td.log_height);
            b.failures.push(msg.clone());
            panic!("{msg}");
        }
    }
    // proof shape (static: depends on the vk and the trace heights only) also rejects a
    // first-order O-2 round 0 when there is more than one commitment
    let layouts = verify_proof_shape::<SC>(mvk, proof).expect("proof shape");
    // Native check `TraceHeightsTooLarge` (verifier/mod.rs): the LogUp count constraints
    // sum_a coeff_a * 2^max(log_height_a, l_skip) < threshold.  The heights are constants of
    // the generated program, so the check is static: a program is only generated for heights
    // that pass it (FAITHFUL.md, finding B2).
    for c in &mvk.trace_height_constraints {
        let sum: u64 = (0..num_airs)
            .map(|a| (1u64 << proof.trace_vdata[a].as_ref().unwrap().log_height.max(l_skip)) * c.coefficients[a] as u64)
            .sum();
        assert!(sum < c.threshold as u64, "child trace heights violate a LogUp count constraint");
    }

    let mut tid: Vec<usize> = (0..num_airs).collect();
    tid.sort_by_key(|&a| (Reverse(proof.trace_vdata[a].as_ref().unwrap().log_height), a));
    let n_per_trace: Vec<usize> = tid
        .iter()
        .map(|&a| proof.trace_vdata[a].as_ref().unwrap().log_height - l_skip)
        .collect();
    let omega_skip = F::two_adic_generator(l_skip);
    let omega_skip_pows: Vec<F> = omega_skip.powers().take(1 << l_skip).collect();

    // ---- preamble ----
    b.const_commit(vk.pre_hash);
    let main_commit = b.load_commit(proof.common_main_commit);
    let mut pv_cells: Vec<Vec<V>> = vec![];
    // per AIR: extra commitments in opening order (preprocessed constant, then cached witnesses)
    let mut extra_commits: Vec<Vec<DigestCells>> = vec![vec![]; num_airs];
    // P4: every cached commitment in preamble order, with its already-loaded cells, so the
    // statement digest can cover them without loading them twice.
    let mut cached_cells: Vec<DigestCells> = vec![];
    let mut cached_limbs: Vec<[F; super::fmt::NV_DIGEST]> = vec![];
    for (a, avk) in mvk.per_air.iter().enumerate() {
        if !avk.is_required {
            let one = b.c(F::ONE);
            b.obs1(one);
        }
        if let Some(pd) = &avk.preprocessed_data {
            // native: the preprocessed commitment is observed instead of log_height
            extra_commits[a].push(b.const_commit(pd.commit));
        } else {
            let lh = proof.trace_vdata[a].as_ref().unwrap().log_height;
            let lhv = b.cu(lh as u64);
            b.obs1(lhv);
        }
        // tight-heights lever: the committed height is observed after log_height
        if let Some(h) = proof.trace_vdata[a].as_ref().unwrap().tight_height {
            let hv = b.cu(h as u64);
            b.obs1(hv);
        }
        let cached = &proof.trace_vdata[a].as_ref().unwrap().cached_commitments;
        assert_eq!(cached.len(), avk.params.width.cached_mains.len(), "cached commitments (proof shape)");
        for &c in cached {
            let cells = b.load_commit(c);
            extra_commits[a].push(cells);
            cached_cells.push(cells);
            cached_limbs.push(super::fmt::digest_limbs(c));
        }
        pv_cells.push(
            proof.public_values[a]
                .iter()
                .map(|&pv| b.load_obs_f(pv))
                .collect(),
        );
    }

    // ---- zerocheck + logup (batch_constraints.rs) ----
    let gkr = &proof.gkr_proof;
    let bp = &proof.batch_constraint_proof;
    let mut pow_id = 0u32;
    pow_check(b, params.logup.pow_bits, gkr.logup_pow_witness, &mut pow_id);
    let alpha_logup = b.smp12();
    let beta_logup = b.smp12();
    let total_interactions: u64 = tid
        .iter()
        .zip(&n_per_trace)
        .map(|(&a, &n)| {
            (mvk.per_air[a].symbolic_constraints.interactions.len() as u64) << (l_skip + n)
        })
        .sum();
    let n_logup = calculate_n_logup(l_skip, total_interactions);
    let mut xi: Vec<V> = vec![];
    let mut p_xi_claim = b.c(F::ZERO);
    let mut q_xi_claim = alpha_logup;
    if total_interactions > 0 {
        let total_rounds = l_skip + n_logup;
        let lv = params.whir.levers;
        let (gruen, derive) = (lv.gruen_gkr, lv.gkr_derive_claims);
        // claims are loaded (not observed); observation order is the native one
        let load_claims = |b: &mut Builder, lc: &openvm_stark_backend::proof::GkrLayerClaims<SC>| {
            let p0 = b.load(lc.p_xi_0);
            let q0 = b.load(lc.q_xi_0);
            let p1 = b.load(lc.p_xi_1);
            let q1 = b.load(lc.q_xi_1);
            (p0, q0, p1, q1)
        };
        let obs_claims = |b: &mut Builder, (p0, q0, p1, q1): (V, V, V, V)| {
            b.obs12(p0);
            b.obs12(q0);
            b.obs12(p1);
            b.obs12(q1);
        };
        let cross = |b: &mut Builder, (p0, q0, p1, q1): (V, V, V, V)| {
            let a = b.mul(p0, q1);
            let c = b.mul(p1, q0);
            let pc = b.add(a, c);
            let qc = b.mul(q0, q1);
            (pc, qc)
        };
        let lc = &gkr.claims_per_layer[0];
        let mut c0 = load_claims(b, lc);
        let q0 = if derive {
            // derived claims: p_xi_1 = -p_xi_0 q_xi_1 / q_xi_0, q0 = q_xi_0 q_xi_1 (zero in proof)
            b.zero(c0.2, "derived p_xi_1 must be zero in the proof");
            let z = b.load(gkr.q0_claim);
            b.zero(z, "derived q0 must be zero in the proof");
            let iq = inv_checked(b, c0.1, "gkr root q_xi_0 inverse");
            let t = b.mul(c0.0, c0.3);
            let t = b.mul(t, iq);
            c0.2 = b.neg(t);
            b.mul(c0.1, c0.3)
        } else {
            b.load(gkr.q0_claim)
        };
        b.obs12(q0);
        obs_claims(b, c0);
        let (pc, qc) = cross(b, c0);
        b.zero(pc, "gkr root zero-check");
        b.assert_eq(qc, q0, "gkr root q0");
        let mu = b.smp12();
        let mut numer = interp_linear(b, c0.0, c0.2, mu);
        let mut denom = interp_linear(b, c0.1, c0.3, mu);
        let mut gkr_r = vec![mu];
        for round in 1..total_rounds {
            let lambda = b.smp12();
            let ld = b.mul(lambda, denom);
            let mut claim = b.add(numer, ld);
            let polys = &gkr.sumcheck_polys[round - 1];
            let mut round_r = vec![];
            let mut eq = b.c(F::ONE);
            for (sr, evals) in polys.iter().enumerate() {
                let e1 = b.load_obs(evals[0]);
                let e2 = b.load_obs(evals[1]);
                let e3 = if gruen {
                    let z = b.load(evals[2]);
                    b.zero(z, "gruen s(3) must be zero in the proof");
                    z
                } else {
                    b.load_obs(evals[2])
                };
                let ri = b.smp12();
                round_r.push(ri);
                let e0 = b.sub(claim, e1);
                if gruen {
                    // s(X) = eq * eq1(xi, X) * t(X), t quadratic
                    let xi_t = gkr_r[sr];
                    let mut tv = vec![];
                    for (k, ek) in [(0u64, e0), (1, e1), (2, e2)] {
                        let kc = b.cu(k);
                        let e1k = eq1(b, xi_t, kc);
                        let d = b.mul(eq, e1k);
                        let id = inv_checked(b, d, "gruen gkr denominator");
                        tv.push(b.mul(ek, id));
                    }
                    let tr = interp_quadratic(b, [tv[0], tv[1], tv[2]], ri);
                    let e1r = eq1(b, xi_t, ri);
                    let t = b.mul(eq, e1r);
                    claim = b.mul(t, tr);
                } else {
                    claim = interp_cubic(b, [e0, e1, e2, e3], ri);
                }
                let e = eq1(b, gkr_r[sr], ri);
                eq = b.mul(eq, e);
            }
            let mut cl = load_claims(b, &gkr.claims_per_layer[round]);
            if derive {
                b.zero(cl.2, "derived p_xi_1 must be zero in the proof");
                // p_xi_1 = (claim / eq - lambda q0 q1 - p0 q1) / q0
                let ie = inv_checked(b, eq, "gkr eq inverse");
                let iq = inv_checked(b, cl.1, "gkr q_xi_0 inverse");
                let ce = b.mul(claim, ie);
                let qq = b.mul(cl.1, cl.3);
                let lqq = b.mul(lambda, qq);
                let pq = b.mul(cl.0, cl.3);
                let t = b.sub(ce, lqq);
                let t = b.sub(t, pq);
                cl.2 = b.mul(t, iq);
            }
            obs_claims(b, cl);
            let (pc, qc) = cross(b, cl);
            let lq = b.mul(lambda, qc);
            let s = b.add(pc, lq);
            let expected = b.mul(s, eq);
            b.assert_eq(expected, claim, "gkr layer");
            let mu = b.smp12();
            numer = interp_linear(b, cl.0, cl.2, mu);
            denom = interp_linear(b, cl.1, cl.3, mu);
            gkr_r = std::iter::once(mu).chain(round_r).collect();
        }
        p_xi_claim = numer;
        q_xi_claim = denom;
        xi = gkr_r;
    } else {
        let q0 = b.load(gkr.q0_claim);
        let one = b.c(F::ONE);
        b.assert_eq(q0, one, "q0 = 1 without interactions");
    }
    let n_max = *n_per_trace.iter().max().unwrap();
    let n_global = n_max.max(n_logup);
    while xi.len() != l_skip + n_global {
        let s = b.smp12();
        xi.push(s);
    }
    let lambda = b.smp12();
    let mut terms = vec![];
    for (&p, &q) in bp
        .numerator_term_per_air
        .iter()
        .zip(&bp.denominator_term_per_air)
    {
        let pv = b.load_obs(p);
        let qv = b.load_obs(q);
        p_xi_claim = b.sub(p_xi_claim, pv);
        q_xi_claim = b.sub(q_xi_claim, qv);
        terms.push((pv, qv));
    }
    b.zero(p_xi_claim, "gkr numerator");
    b.assert_eq(q_xi_claim, alpha_logup, "gkr denominator");
    let mu = b.smp12();
    let mut sum_claim = b.c(F::ZERO);
    let mut mp = b.c(F::ONE);
    for &(p, q) in &terms {
        let t = b.mul(p, mp);
        sum_claim = b.add(sum_claim, t);
        mp = b.mul(mp, mu);
        let t = b.mul(q, mp);
        sum_claim = b.add(sum_claim, t);
        mp = b.mul(mp, mu);
    }
    let ucoeffs: Vec<V> = bp
        .univariate_round_coeffs
        .iter()
        .map(|&c| b.load_obs(c))
        .collect();
    let s_deg = params.max_constraint_degree + 1;
    let r0 = b.smp12();
    let stepped: Vec<V> = ucoeffs.iter().step_by(1 << l_skip).copied().collect();
    let ssum = sum(b, &stepped);
    let ssum = b.mul_c(ssum, F::from_usize(1 << l_skip));
    b.assert_eq(sum_claim, ssum, "univariate sum");
    let mut cur_sum = horner(b, &ucoeffs, r0);
    let mut rs = vec![r0];
    let mut factorials = vec![F::ONE; s_deg + 1];
    for i in 1..=s_deg {
        factorials[i] = factorials[i - 1] * F::from_usize(i);
    }
    let invfact = batch_multiplicative_inverse(&factorials);
    let gruen_rounds = if params.whir.levers.gruen_zerocheck {
        n_per_trace.iter().copied().min().unwrap_or(0).min(n_max)
    } else {
        0
    };
    // Lagrange weights at x = s_deg over the points 0..s_deg-1 (constants)
    let lag_at_sdeg: Vec<F> = (0..s_deg)
        .map(|k| {
            let mut num = F::ONE;
            let mut den = F::ONE;
            for j in 0..s_deg {
                if j != k {
                    num *= F::from_usize(s_deg) - F::from_usize(j);
                    den *= F::from_usize(k) - F::from_usize(j);
                }
            }
            num * den.inverse()
        })
        .collect();
    for round in 0..n_max {
        let gruen = round < gruen_rounds;
        let raw = &bp.sumcheck_round_polys[round];
        let mut evals: Vec<V> = raw[..raw.len() - gruen as usize]
            .iter()
            .map(|&e| b.load_obs(e))
            .collect();
        if gruen {
            let z = b.load(*raw.last().unwrap());
            b.zero(z, "gruen zerocheck last eval must be zero in the proof");
            // s(X) = eq1(xi, X) s'(X): s'(k) = s(k) / eq1(k), s(s_deg) = eq1(s_deg) s'(s_deg)
            let xi_cur = xi[l_skip + round];
            let s0g = b.sub(cur_sum, evals[0]);
            let mut acc = b.c(F::ZERO);
            for k in 0..s_deg {
                let sk = if k == 0 { s0g } else { evals[k - 1] };
                let kc = b.cu(k as u64);
                let ek = eq1(b, xi_cur, kc);
                let ik = inv_checked(b, ek, "gruen zerocheck eq1 inverse");
                let spk = b.mul(sk, ik);
                let t = b.mul_c(spk, lag_at_sdeg[k]);
                acc = b.add(acc, t);
            }
            let xs = b.cu(s_deg as u64);
            let es = eq1(b, xi_cur, xs);
            evals.push(b.mul(es, acc));
        }
        let s0 = b.sub(cur_sum, evals[0]);
        let all: Vec<V> = std::iter::once(s0).chain(evals).collect();
        let r = b.smp12();
        let one = b.c(F::ONE);
        let mut pref = vec![one; s_deg + 1];
        let mut suf = vec![one; s_deg + 1];
        for i in 0..s_deg {
            let a = b.add_c(r, -F::from_usize(i));
            pref[i + 1] = b.mul(pref[i], a);
            let k = b.cu((s_deg - i) as u64);
            let c = b.sub(k, r);
            suf[i + 1] = b.mul(suf[i], c);
        }
        let mut acc = b.c(F::ZERO);
        for i in 0..=s_deg {
            let t = b.mul(all[i], pref[i]);
            let t = b.mul(t, suf[s_deg - i]);
            let t = b.mul_c(t, invfact[i] * invfact[s_deg - i]);
            acc = b.add(acc, t);
        }
        cur_sum = acc;
        rs.push(r);
    }
    // eq_3b
    let mut stacked_idx = 0usize;
    let eq_3b: Vec<Vec<V>> = n_per_trace
        .iter()
        .enumerate()
        .map(|(t, &n)| {
            let ints = &mvk.per_air[tid[t]].symbolic_constraints.interactions;
            (0..ints.len())
                .map(|_| {
                    let mut b_int = stacked_idx >> (l_skip + n);
                    let bits: Vec<bool> = (0..n_logup - n)
                        .map(|_| {
                            let bit = b_int & 1 == 1;
                            b_int >>= 1;
                            bit
                        })
                        .collect();
                    stacked_idx += 1 << (l_skip + n);
                    eq_mle_bits(b, &xi[l_skip + n..l_skip + n_logup], &bits)
                })
                .collect()
        })
        .collect();
    // eq_ns, eq_sharp_ns
    let mut eq_ns = vec![b.c(F::ONE); n_max + 1];
    let mut eq_sharp = vec![b.c(F::ONE); n_max + 1];
    eq_ns[0] = eq_uni(b, l_skip, xi[0], r0);
    {
        // eval_eq_sharp_uni(omega_skip_pows, xi[..l_skip], r0)
        let n = 1 << l_skip;
        let mut evals = vec![b.c(F::ONE)];
        for i in 0..l_skip {
            let mut next = vec![b.c(F::ZERO); 2 * evals.len()];
            let om = b.one_minus(xi[i]);
            for (j, &e) in evals.iter().enumerate() {
                next[j] = b.mul(e, om);
                next[j + evals.len()] = b.mul(e, xi[i]);
            }
            evals = next;
        }
        let mut res = b.c(F::ZERO);
        for k in 0..n {
            let wv = b.c(omega_skip_pows[k]);
            let e = eq_uni(b, l_skip, r0, wv);
            let t = b.mul(e, evals[k]);
            res = b.add(res, t);
        }
        eq_sharp[0] = res;
    }
    for i in 1..=n_max {
        let e = eq1(b, xi[l_skip + i - 1], rs[i]);
        eq_ns[i] = b.mul(eq_ns[i - 1], e);
        eq_sharp[i] = b.mul(eq_sharp[i - 1], e);
    }
    let mut rrev = rs[n_max];
    for i in (0..n_max).rev() {
        eq_ns[i] = b.mul(eq_ns[i], rrev);
        eq_sharp[i] = b.mul(eq_sharp[i], rrev);
        rrev = b.mul(rrev, rs[i]);
    }
    // column openings: observe (all common main first)
    // per trace, per common-main column: rotated opening present (next_mask lever / need_rot)
    let all_masks: Vec<Vec<Vec<bool>>> = tid.iter().map(|&a| mvk.per_air[a].params.opening_masks()).collect();
    let masks: Vec<Vec<bool>> = all_masks.iter().map(|m| m[0].clone()).collect();
    let load_part = |b: &mut Builder, part: &[EF], mask: &[bool]| -> Vec<(V, V)> {
        openvm_stark_backend::proof::column_openings_by_mask(part, mask)
            .into_iter()
            .zip(mask)
            .map(|((c, r), &m)| {
                let cv = b.load_obs(c);
                let rv = if m {
                    b.load_obs(r)
                } else {
                    let z = b.c(F::ZERO);
                    b.obs12(z)
                };
                (cv, rv)
            })
            .collect()
    };
    let mut open_cells: Vec<Vec<(V, V)>> = vec![];
    for (t, parts) in bp.column_openings.iter().enumerate() {
        open_cells.push(load_part(b, &parts[0], &masks[t]));
    }
    // then, per trace, its other parts (preprocessed, cached) in opening order (native
    // batch_constraints: observed per trace before its evaluation; nothing is sampled between)
    let mut part_cells: Vec<Vec<Vec<(V, V)>>> = vec![];
    for (t, parts) in bp.column_openings.iter().enumerate() {
        part_cells.push(parts[1..].iter().zip(&all_masks[t][1..]).map(|(p, m)| load_part(b, p, m)).collect());
    }
    b.dbg_rs = rs.iter().map(|v| v.val).collect();
    b.dbg_tid = tid.clone();
    b.dbg_openings = open_cells
        .iter()
        .map(|cs| cs.iter().map(|(c, _)| c.val).collect())
        .collect();
    if b.agg {
        // [agg] the aggregation program exposes level and statement itself (nv/agg.rs)
    } else if b.bind {
        // child is NV: level = child level + 1; BIND enforced iff child level != M (the anchor
        // level; M = 1 unless the program converges later, see `NvCircuit::anchor`)
        let cl = pv_cells[0][0];
        let one = b.c(F::ONE);
        let own = b.add(cl, one);
        b.pv_level(own);
        let m_level = b.anchor.map_or(1, |(m, _)| m);
        let mc = b.c(F::from_u32(m_level));
        let clm1 = b.sub(cl, mc);
        let cv = coeffs(clm1.val)[0];
        let inv = b.load_f(if cv == F::ZERO { F::ZERO } else { cv.inverse() });
        let flag = b.mul(clm1, inv);
        let nf = b.one_minus(flag);
        let t = b.mul(clm1, nf);
        b.zero(t, "level flag");
        // G2: the child's program columns: its cached program part (NV levels) or, for a child
        // without one, its common main P0..P3
        let tc = tid.iter().position(|&a| a == 0).expect("child ALU");
        let child_prog_part = !mvk.per_air[0].params.width.cached_mains.is_empty();
        let prog_open: Vec<V> = if child_prog_part {
            let has_prep = mvk.per_air[0].preprocessed_data.is_some() as usize;
            (0..4).map(|j| part_cells[tc][has_prep][j].0).collect()
        } else {
            (0..4).map(|j| open_cells[tc][super::uair::U_P + j].0).collect()
        };
        // anchor-level child (flag = 0): its program commitment is the constant C_M, the
        // commitment of the level-M program at these parameters (setup); (root - C_M) (1 - flag) = 0
        if child_prog_part {
            match b.anchor {
                Some((_, c_m)) => {
                    let root = extra_commits[0][0];
                    let nf = b.one_minus(flag);
                    let cm = b.const_digest(c_m);
                    for (x, y) in [(root.lo, cm.lo), (root.hi, cm.hi)] {
                        let d = b.sub(x, y);
                        let t = b.mul(d, nf);
                        b.zero(t, "anchor child program commitment = C_M");
                    }
                    if flag.val == EF::ZERO && root.digest != c_m {
                        b.failures.push("anchor child program commitment != C_M".into());
                    }
                }
                None => b.failures.push("no anchor constant C_M for an anchor-level child".into()),
            }
        } else if flag.val == EF::ZERO {
            b.failures.push("anchor-level child without a program commitment cannot be bound".into());
        }
        bind_child_program(b, &tid, &n_per_trace, &rs, &prog_open, l_skip, flag);
    } else {
        let one = b.c(F::ONE);
        b.pv_level(one);
    }

    if b.agg {
        // [agg] the aggregation program (nv/agg.rs) exposes its own level and statement; the
        // per-child statement of each child is read from `pv_cells` by the caller.  Exposing
        // anything here would push a second PvD row that contradicts the node's statement.
    } else if b.bind || b.child_nv {
        // statement passthrough (G1): the child's statement digest (its public values 1..19)
        // is re-exposed unchanged
        let pv = &pv_cells[0];
        assert_eq!(pv.len(), super::uair::NV_NUM_PVS, "child is NV");
        let pack = |b: &mut Builder, cells: &[V]| -> V {
            let mut acc = b.c(F::ZERO);
            for (k, &x) in cells.iter().enumerate() {
                let mut basis = [F::ZERO; 12];
                basis[k] = F::ONE;
                let xk = b.ce(ef_from(basis));
                let t = b.mul(x, xk);
                acc = b.add(acc, t);
            }
            acc
        };
        let lo = pack(b, &pv[1..13]);
        let hi = pack(b, &pv[13..19]);
        let limbs: Vec<F> = pv[1..19].iter().map(|v| coeffs(v.val)[0]).collect();
        let d = limbs_digest(&limbs);
        b.pv_digest(&DigestCells { lo, hi, digest: d });
    } else {
        // Statement digest (G1): SHA-384 (tag 8) of the app proof's public values
        let mut cells: Vec<V> = vec![b.c(F::from_usize(pv_cells.len()))];
        for p in &pv_cells {
            let n = b.c(F::from_usize(p.len()));
            cells.push(n);
        }
        cells.extend(pv_cells.iter().flatten().copied());
        let job = b.job_start(crate::sha384::config::TAG_STATEMENT, 4 * cells.len());
        for (i, &x) in cells.iter().enumerate() {
            b.unit1(x, job, 2 + i as u32);
        }
        let d = crate::sha384::config::statement_digest(&proof.public_values);
        let mut dc = b.dig(job, d);
        // P4/M2: the cached commitments (TAPE, the join's host-wire tables) are proof values, not
        // public values, so the statement must cover them or V_d would accept a base whose cached
        // table was anything.  Each one is chained into the digest with the Merkle-node
        // compression the SHA subsystem already checks (`node`: 8 + 2w bytes, one compression),
        // rather than appended as more statement bytes: an NV leaf job hashes one block, and the
        // app statement message is already close to 128 bytes.  With no cached commitment the
        // chain is empty, so the statement is the G1 one unchanged (inert for the G2 gate).
        for root in &cached_cells {
            dc = b.node(&dc, root);
        }
        b.pv_digest(&dc);
    }
    eprintln!("NV_PHASE before_dag {}", b.instrs.len());
    // per-trace constraint and interaction evaluation
    let omega = F::two_adic_generator(l_skip);
    let inv_n = F::from_usize(1 << l_skip).inverse();
    let mut inter_evals = vec![];
    let mut constr_evals = vec![];
    for (t, &n) in n_per_trace.iter().enumerate() {
        let a = tid[t];
        let trace_t = t;
        let avk = &mvk.per_air[a];
        let rs_n = &rs[..=n];
        // is_first_row / is_last_row
        let prog = |b: &mut Builder, m: V| {
            let ms = powers_of_2(b, m, l_skip);
            let mut acc = b.c(F::ONE);
            for mp in ms {
                let t = b.add_c(mp, F::ONE);
                acc = b.mul(acc, t);
            }
            acc
        };
        let pf = prog(b, rs_n[0]);
        let mut pfirst = b.mul_c(pf, inv_n);
        for &x in &rs_n[1..] {
            let om = b.one_minus(x);
            pfirst = b.mul(pfirst, om);
        }
        let r0w = b.mul_c(rs_n[0], omega);
        let pl = prog(b, r0w);
        let mut plast = b.mul_c(pl, inv_n);
        for &x in &rs_n[1..] {
            plast = b.mul(plast, x);
        }
        let ptrans = b.one_minus(plast);
        let cells = &open_cells[t];
        let has_prep = avk.preprocessed_data.is_some() as usize;
        let n_cached = avk.params.width.cached_mains.len();
        let dag = &avk.symbolic_constraints.constraints;
        let mut nodes: Vec<V> = Vec::with_capacity(dag.nodes.len());
        for node in &dag.nodes {
            let v = match node {
                SymbolicExpressionNode::Variable(var) => match var.entry {
                    // native evaluator: partitioned main = cached parts, then common main last
                    Entry::Main { part_index, offset } => {
                        let pc = if part_index == n_cached {
                            cells
                        } else {
                            assert!(part_index < n_cached, "main part index");
                            &part_cells[t][has_prep + part_index]
                        };
                        if offset == 0 {
                            pc[var.index].0
                        } else {
                            pc[var.index].1
                        }
                    }
                    Entry::Preprocessed { offset } => {
                        assert!(has_prep == 1, "preprocessed variable without a preprocessed trace");
                        let pc = &part_cells[t][0];
                        if offset == 0 {
                            pc[var.index].0
                        } else {
                            pc[var.index].1
                        }
                    }
                    Entry::Public => pv_cells[a][var.index],
                    e => panic!("unsupported entry {e:?}"),
                },
                SymbolicExpressionNode::Constant(c) => b.c(*c),
                SymbolicExpressionNode::Add {
                    left_idx,
                    right_idx,
                    ..
                } => b.add(nodes[*left_idx], nodes[*right_idx]),
                SymbolicExpressionNode::Sub {
                    left_idx,
                    right_idx,
                    ..
                } => b.sub(nodes[*left_idx], nodes[*right_idx]),
                SymbolicExpressionNode::Neg { idx, .. } => b.neg(nodes[*idx]),
                SymbolicExpressionNode::Mul {
                    left_idx,
                    right_idx,
                    ..
                } => b.mul(nodes[*left_idx], nodes[*right_idx]),
                SymbolicExpressionNode::IsFirstRow => pfirst,
                SymbolicExpressionNode::IsLastRow => plast,
                SymbolicExpressionNode::IsTransition => ptrans,
            };
            nodes.push(v);
        }
        let mut expr = b.c(F::ZERO);
        let mut lp = b.c(F::ONE);
        for &idx in &dag.constraint_idx {
            let t = b.mul(nodes[idx], lp);
            expr = b.add(expr, t);
            lp = b.mul(lp, lambda);
        }
        constr_evals.push(b.mul(eq_ns[n], expr));
        eprintln!("NV_DAG air={a} nodes={} rows_so_far={}", dag.nodes.len(), b.instrs.len());
        let mut num = b.c(F::ZERO);
        let mut den = b.c(F::ZERO);
        for (i, inter) in avk.symbolic_constraints.interactions.iter().enumerate() {
            let cnt = nodes[inter.count];
            let mut d = b.c(F::ZERO);
            let mut bp_ = b.c(F::ONE);
            for &f in &inter.message {
                let t = b.mul(nodes[f], bp_);
                d = b.add(d, t);
                bp_ = b.mul(bp_, beta_logup);
            }
            let busv = b.cu(inter.bus_index as u64 + 1);
            let t = b.mul(busv, bp_);
            d = b.add(d, t);
            let w = eq_3b[trace_t][i];
            let tn = b.mul(w, cnt);
            num = b.add(num, tn);
            let td = b.mul(w, d);
            den = b.add(den, td);
        }
        let nn = b.mul(num, eq_sharp[n]);
        inter_evals.push(nn);
        inter_evals.push(b.mul(den, eq_sharp[n]));
    }
    let mut evaluated = b.c(F::ZERO);
    let mut mp = b.c(F::ONE);
    for &x in inter_evals.iter().chain(constr_evals.iter()) {
        let t = b.mul(x, mp);
        evaluated = b.add(evaluated, t);
        mp = b.mul(mp, mu);
    }
    b.assert_eq(cur_sum, evaluated, "batch constraint claim");
    eprintln!("NV_PHASE after_dag {}", b.instrs.len());

    // ---- stacked reduction ----
    let sp = &proof.stacking_proof;
    // claims: commit 0 (every trace's common main), then commits 1.. (per trace, its other parts)
    let mut t_claims: Vec<(V, V)> = open_cells.iter().flatten().copied().collect();
    t_claims.extend(part_cells.iter().flatten().flatten().copied());
    let lambda_s = b.smp12();
    let lambda2 = b.square(lambda_s);
    let mut l2p = vec![];
    let mut p = b.c(F::ONE);
    for _ in 0..t_claims.len() {
        l2p.push(p);
        p = b.mul(p, lambda2);
    }
    let mut s0 = b.c(F::ZERO);
    for (i, &(c, r)) in t_claims.iter().enumerate() {
        let t = b.mul(r, lambda_s);
        let t = b.add(c, t);
        let t = b.mul(t, l2p[i]);
        s0 = b.add(s0, t);
    }
    let scoeffs: Vec<V> = sp
        .univariate_round_coeffs
        .iter()
        .map(|&c| b.load(c))
        .collect();
    let stepped: Vec<V> = scoeffs.iter().step_by(1 << l_skip).copied().collect();
    let ss = sum(b, &stepped);
    let ss = b.mul_c(ss, F::from_usize(1 << l_skip));
    b.assert_eq(s0, ss, "stacking s0");
    for &c in &scoeffs {
        b.obs12(c);
    }
    let n_stack = params.n_stack;
    let mut u = vec![b.smp12()];
    let mut claim = horner(b, &scoeffs, u[0]);
    for j in 1..=n_stack {
        let s1 = b.load_obs(sp.sumcheck_round_polys[j - 1][0]);
        let s2 = b.load_obs(sp.sumcheck_round_polys[j - 1][1]);
        let uj = b.smp12();
        u.push(uj);
        let sj0 = b.sub(claim, s1);
        claim = interp_quadratic(b, [sj0, s1, s2], uj);
    }
    // q_coeffs: kernels depend only on (n, need_rot); cache per n.
    let zero = b.c(F::ZERO);
    let mut qcs: Vec<Vec<V>> = sp.stacking_openings.iter().map(|o| vec![zero; o.len()]).collect();
    let om_u: Vec<V> = u.iter().map(|&x| b.one_minus(x)).collect();
    // per commit: the masks of its matrices (commit 0: every trace's common main; commits 1..:
    // one matrix each, per trace in sorted order its preprocessed then cached parts)
    let mut commit_masks: Vec<Vec<Vec<bool>>> = vec![masks.clone()];
    for m in &all_masks {
        for pm in &m[1..] {
            commit_masks.push(vec![pm.clone()]);
        }
    }
    assert_eq!(commit_masks.len(), layouts.len(), "commitments (proof shape)");
    // kernels and the eq memo depend on (u, r, lambda) and the slice position only, so they
    // are shared between commitments
    let mut kern: std::collections::BTreeMap<(usize, bool, usize, usize), V> = Default::default();
    let mut em_memo: std::collections::HashMap<(usize, usize), V> = Default::default();
    let mut lambda_base = 0usize;
    for ((layout, cmasks), qc) in layouts.iter().zip(&commit_masks).zip(qcs.iter_mut()) {
    // claim index of (mat, col): position in (matrix, column) order (tight chunks share it)
    let mut col_base = vec![];
    {
        let mut acc = lambda_base;
        for m in cmasks {
            col_base.push(acc);
            acc += m.len();
        }
        lambda_base = acc;
    }
    for &(mat_idx, col_idx, s) in layout.sorted_cols.iter() {
        let need = cmasks[mat_idx][col_idx];
        let n = s.log_height() - l_skip;
        let key = (n, need, s.src_row, s.col_log_height());
        if !kern.contains_key(&key) {
            let rs_n = &rs[..=n];
            let eu = eq_uni(b, l_skip, u[0], rs_n[0]);
            let emr = eq_mle(b, &u[1..=n], &rs_n[1..]);
            let eq_prism = b.mul(eu, emr);
            // chunk factors (c, delta) of the tight-heights lever ((1, 0) for whole columns)
            let whole = s.src_row == 0 && s.col_log_height() == s.log_height();
            let (cf, delta) = if whole {
                (None, None)
            } else {
                let m = s.log_height() - l_skip;
                let n_t = s.col_log_height() - l_skip;
                let o = s.src_row >> l_skip;
                let eqb = |b: &mut Builder, bit: usize, r: V| if bit == 1 { r } else { b.one_minus(r) };
                let mut c = b.c(F::ONE);
                for t in m..n_t {
                    let e = eqb(b, (o >> t) & 1, rs[1 + t]);
                    c = b.mul(c, e);
                }
                let prev = (o + (1 << n_t) - 1) & ((1 << n_t) - 1);
                let mut ep = b.c(F::ONE);
                for t in 0..n_t {
                    let e = eqb(b, (prev >> t) & 1, rs[1 + t]);
                    ep = b.mul(ep, e);
                }
                let mut ones = b.c(F::ONE);
                for t in 0..m {
                    ones = b.mul(ones, rs[1 + t]);
                }
                let co = b.mul(c, ones);
                (Some(c), Some(b.sub(ep, co)))
            };
            let mut kv = match cf { Some(c) => b.mul(c, eq_prism), None => eq_prism };
            if need {
                let mut rot = b.c(F::ONE);
                let mut eqc = b.c(F::ONE);
                for i in (1..=n).rev() {
                    let x = u[i];
                    let y = rs_n[i];
                    let oy = b.one_minus(y);
                    let t1 = b.mul(x, oy);
                    let t1 = b.mul(t1, eqc);
                    let t2 = b.mul(om_u[i], y);
                    let t2 = b.mul(t2, rot);
                    rot = b.add(t1, t2);
                    let e = eq1(b, x, y);
                    eqc = b.mul(eqc, e);
                }
                let yw = b.mul_c(rs_n[0], omega);
                let a1 = eq_uni(b, l_skip, u[0], yw);
                let a1 = b.mul(a1, eqc);
                let b1 = eq_uni_at_one(b, l_skip, u[0]);
                let b2 = eq_uni_at_one(b, l_skip, yw);
                let d = b.sub(rot, eqc);
                let bb = b.mul(b1, b2);
                let bb = b.mul(bb, d);
                let mut rk = b.add(a1, bb);
                if let (Some(c), Some(delta)) = (cf, delta) {
                    // c * rot kernel + eq_D(w r0, 1) eq_D(u0, 1) prod (1 - u_t) delta
                    let mut corr = b.mul(b1, b2);
                    for t in 1..=n {
                        corr = b.mul(corr, om_u[t]);
                    }
                    let corr = b.mul(corr, delta);
                    let crk = b.mul(c, rk);
                    rk = b.add(crk, corr);
                }
                let lrk = b.mul(lambda_s, rk);
                kv = b.add(kv, lrk);
            }
            kern.insert(key, kv);
        }
        let kv = kern[&key];
        // eq of the slice's stacked row bits above its height, memoized on (start bit, high bits)
        let em = {
            let mut j = l_skip + n_stack;
            let mut chain = vec![];
            for jj in (l_skip + n..l_skip + n_stack).rev() {
                chain.push(jj);
            }
            let mut acc_v: Option<V> = None;
            for jj in chain {
                let hi = s.row_idx >> jj;
                let k = (jj, hi);
                let v = if let Some(&v) = em_memo.get(&k) {
                    v
                } else {
                    let i = jj - (l_skip + n);
                    let _ = i;
                    let f = if hi & 1 == 1 { u[jj - l_skip + 1] } else { om_u[jj - l_skip + 1] };
                    let v = match acc_v { Some(a) => b.mul(a, f), None => f };
                    em_memo.insert(k, v);
                    v
                };
                acc_v = Some(v);
                j = jj;
            }
            let _ = j;
            acc_v.unwrap_or_else(|| b.c(F::ONE))
        };
        let t = b.mul(em, kv);
        let t = b.mul(t, l2p[col_base[mat_idx] + col_idx]);
        qc[s.col_idx] = b.add(qc[s.col_idx], t);
    }
    }
    assert_eq!(lambda_base, t_claims.len());
    // stacking openings of every commitment, in commit order (one flat list, as WHIR batches it)
    let widths: Vec<usize> = sp.stacking_openings.iter().map(|o| o.len()).collect();
    let stack_open: Vec<V> = sp.stacking_openings
        .iter()
        .flatten()
        .map(|&q| b.load_obs(q))
        .collect();
    let mut final_sum = b.c(F::ZERO);
    for (q, o) in qcs.iter().flatten().zip(&stack_open) {
        let t = b.mul(*q, *o);
        final_sum = b.add(final_sum, t);
    }
    b.assert_eq(claim, final_sum, "stacking final sum");

    eprintln!("NV_PHASE after_stacking {}", b.instrs.len());
    // ---- WHIR ----
    let u_cube: Vec<V> = {
        let mut v = powers_of_2(b, u[0], l_skip);
        v.extend(&u[1..]);
        v
    };
    // WHIR round-0 trees: common main, then the extra commitments in sorted trace order
    let mut roots = vec![main_commit];
    for &a in &tid {
        roots.extend(extra_commits[a].iter().copied());
    }
    assert_eq!(roots.len(), layouts.len());
    whir(b, vk, proof, &stack_open, &widths, &roots, &u_cube, &mut pow_id);
    eprintln!("NV_PHASE end {}", b.instrs.len());
    pv_cells
}

/// Program binding (DESIGN §2.1): the child's ALU (air 0) program columns P0..P3 must
/// equal this program.  Fills the reserved E1/E2 rows with the row weights
/// w(x) = L_{x mod 2^l}(r0) * eq(r_1.., bits(x >> l)) and checks
/// sum_x w(x) sum_j tau^j P_j[x] (the ACC row) == sum_j tau^j open(P_j).
fn bind_child_program(
    b: &mut Builder,
    tid: &[usize],
    n_per_trace: &[usize],
    rs: &[V],
    prog_open: &[V],
    l_skip: usize,
    flag: V,
) {
    use super::uair::{tau_pows, E1_BITS, E1_SIZE};
    let t = tid.iter().position(|&a| a == 0).expect("child ALU");
    let n = n_per_trace[t];
    assert_eq!(l_skip + n, b.log_rows, "child ALU height must equal ours");
    let omega = F::two_adic_generator(l_skip);
    let lv: Vec<V> = (0..1usize << l_skip)
        .map(|i| {
            let w = b.c(omega.exp_u64(i as u64));
            eq_uni(b, l_skip, rs[0], w)
        })
        .collect();
    // eq table over r[1..=m1], m1 = E1_BITS - l_skip (LSB = r[1])
    let eq_table = |b: &mut Builder, vars: &[V]| -> Vec<V> {
        let mut tab = vec![b.c(F::ONE)];
        for &r in vars {
            let om = b.one_minus(r);
            let mut next = Vec::with_capacity(2 * tab.len());
            for &e in &tab {
                next.push(b.mul(e, om));
            }
            for &e in &tab {
                next.push(b.mul(e, r));
            }
            tab = next;
        }
        tab
    };
    let m1 = E1_BITS - l_skip;
    let t1 = eq_table(b, &rs[1..=m1]);
    // ALU rows are [0, prog_len): only E2 entries with every index bit above prog_log zero are
    // used, so E2 is the table over the prog_log - E1_BITS middle variables and the factor
    // prod (1 - r) of the top variables is folded into the 2^l_skip Lagrange values
    let m2u = b.prog_log - E1_BITS;
    let mut top = b.c(F::ONE);
    for &r in &rs[m1 + 1 + m2u..=n] {
        let om = b.one_minus(r);
        top = b.mul(top, om);
    }
    let lv: Vec<V> = lv.iter().map(|&v| b.mul(v, top)).collect();
    for x in 0..E1_SIZE {
        let (lo, hi) = (x & ((1 << l_skip) - 1), x >> l_skip);
        b.set_reserved_mul(x, lv[lo], t1[hi]);
    }
    let t2 = eq_table(b, &rs[m1 + 1..m1 + 1 + m2u]);
    let one = b.c(F::ONE);
    debug_assert_eq!(b.prog_len() / E1_SIZE, t2.len());
    for x in 0..b.prog_len() / E1_SIZE {
        b.set_reserved_mul(E1_SIZE + x, t2[x], one);
    }
    let tp = tau_pows();
    let mut phat = b.c(F::ZERO);
    for j in 0..4 {
        let tj = b.ce(tp[j]);
        let o = prog_open[j];
        let term = b.mul(tj, o);
        phat = b.add(phat, term);
    }
    // child level != M (flag = 1): BIND, flag (ACC - phat) = 0; an anchor-level child is bound by
    // C_M above (G2: no app table)
    b.defer_acc_check(phat, flag);
}

fn whir(
    b: &mut Builder,
    vk: &MultiStarkVerifyingKey<SC>,
    proof: &Proof<SC>,
    stack_open: &[V],
    widths: &[usize],
    roots: &[DigestCells],
    u: &[V],
    pow_id: &mut u32,
) {
    let params = &vk.inner.params;
    let w = &proof.whir_proof;
    let k = params.k_whir();
    let m = params.l_skip + params.n_stack;
    let num_rounds = params.num_whir_rounds();
    let mut log_rs = m + params.log_blowup;
    let odd = params.whir.domain_odd_factor;
    let shrink = params.whir.domain_shrink();
    let multiproof = params.whir.levers.multiproof;
    let pow_width = 1 + params.whir.levers.wide_query_pow as usize;
    if odd != 1 {
        assert_eq!(odd, 15, "NV supports the x15 domain only");
        let c = b.cu(odd as u64);
        b.obs1(c);
    }
    let _ = k;
    pow_check(b, params.whir.mu_pow_bits, w.mu_pow_witness, pow_id);
    let mu = b.smp12();
    let total_width = stack_open.len();
    let mut mu_pows = vec![b.c(F::ONE)];
    for i in 1..total_width {
        let p = b.mul(mu_pows[i - 1], mu);
        mu_pows.push(p);
    }
    let mut claim = b.c(F::ZERO);
    for (o, mp) in stack_open.iter().zip(&mu_pows) {
        let t = b.mul(*o, *mp);
        claim = b.add(claim, t);
    }
    let mut sc_iter = w.whir_sumcheck_polys.iter();
    let mut fold_pow = w.folding_pow_witnesses.iter();
    let mut gammas = vec![];
    let mut zs: Vec<Vec<V>> = vec![];
    let mut z0s = vec![];
    let mut alphas: Vec<V> = vec![];
    let mut final_poly: Vec<V> = vec![];
    let num_commits = roots.len();
    assert_eq!(widths.len(), num_commits);
    assert_eq!(widths.iter().sum::<usize>(), total_width);
    let mut qid = 0u32;
    let mut round_commits: Vec<DigestCells> = vec![];
    for round in 0..num_rounds {
        let is_initial = round == 0;
        let is_final = round == num_rounds - 1;
        let k = params.whir.k_round(round);
        let mut alphas_round = vec![];
        for _ in 0..k {
            let evals = sc_iter.next().unwrap();
            let e1 = b.load_obs(evals[0]);
            let e2 = b.load_obs(evals[1]);
            pow_check(b, params.whir.folding_pow_bits, *fold_pow.next().unwrap(), pow_id);
            let alpha = b.smp12();
            alphas_round.push(alpha);
            let e0 = b.sub(claim, e1);
            claim = interp_quadratic(b, [e0, e1, e2], alpha);
        }
        let (y0, commit) = if is_final {
            for &c in &w.final_poly {
                final_poly.push(b.load_obs(c));
            }
            (None, None)
        } else {
            let cc = b.load_commit(w.codeword_commits[round]);
            round_commits.push(cc);
            let z0 = b.smp12();
            z0s.push(z0);
            let y0 = b.load_obs(w.ood_values[round]);
            (Some(y0), Some(cc))
        };
        let _ = commit;
        b.pow(
            params.whir.query_phase_pow_bits,
            &w.query_phase_pow_witnesses[round * pow_width..(round + 1) * pow_width],
        );
        let nq = params.whir.rounds[round].num_queries;
        let nbits = log_rs - k;
        let omega = F::two_adic_generator(log_rs);
        let omega_k = F::two_adic_generator(k);
        let mut zs_round = vec![];
        let mut ys_round = vec![];
        let q_start = b.instrs.len();
        // Merkle paths are verified after the round's queries (multiproof needs all leaves)
        // per round-0 tree (one tree in later rounds): (leaf job base, leaf digests, bits, index)
        let mut pending: Vec<Vec<(u32, Vec<crate::sha384::config::Digest>, Vec<V>, usize)>> =
            vec![vec![]; if is_initial { num_commits } else { 1 }];
        let zeta = if odd != 1 { openvm_stark_backend::odd_domain::odd_root::<F>(odd) } else { F::ONE };
        for qi in 0..nq {
            let s = b.smp1();
            let (bits, zi_root, index) = if odd == 1 {
                let bits = decompose_index(b, s, nbits, qid);
                let index = coeffs(s.val)[0].as_canonical_u32() as usize & ((1usize << nbits) - 1);
                let zr = pow_by_bits(b, omega, &bits);
                (bits, zr, index)
            } else {
                let (bits, abits) = decompose_index_x15(b, s, nbits, qid);
                let x = coeffs(s.val)[0].as_canonical_u32() as usize;
                let index = (((x >> nbits) % 15) << nbits) | (x & ((1 << nbits) - 1));
                let wu = pow_by_bits(b, omega, &bits[..nbits]);
                let za = pow_by_bits(b, zeta, &abits);
                (bits, b.mul(wu, za), index)
            };
            let zi = exp_pow2(b, zi_root, k);
            let values: Vec<V> = if is_initial {
                // per commit: leaf jobs (one per coset row, or one coset job); the 2^k values are
                // sum_c mu^c row[c] over the concatenated columns of every commit, by one Horner
                // chain per row from the last column of the last commit down (native
                // codeword_vals: commit t's columns take mu powers after those of commits < t)
                let rows = &w.initial_round_opened_rows;
                // test hook: open query 1's rows at query 0's index
                let qi = if qi == 0 && nq > 1 && tamper_now(Tamper::OtherLeaf) { 1 } else { qi };
                let coset = crate::sha384::config::sha_levers().coset_leaf;
                let mut job_bases = vec![];
                for ct in 0..num_commits {
                    let width_t = rows[ct][qi][0].len();
                    assert_eq!(width_t, widths[ct], "opened row width (proof shape)");
                    job_bases.push(b.job_units.len() as u32);
                    // coset leaf (lever): one tag-6 job holding all 2^k rows; else one job per row
                    if coset {
                        b.job_start(crate::sha384::config::TAG_COSET_LEAF, 4 * width_t << k);
                    } else {
                        for _ in 0..(1 << k) {
                            b.job_start(0, 4 * width_t);
                        }
                    }
                }
                let mut vals = vec![];
                for j in 0..(1 << k) {
                    let mut acc = b.c(F::ZERO);
                    for ct in (0..num_commits).rev() {
                        let r = &rows[ct][qi][j];
                        let width_t = r.len();
                        let job_base = job_bases[ct];
                        let unit = |c: usize| -> (u32, u32) {
                            if coset {
                                (job_base, 2 + (j * width_t + c) as u32)
                            } else {
                                (job_base + j as u32, 2 + c as u32)
                            }
                        };
                        // Horner over the row's felts from the top: two per Horn2 row, the last one
                        // (odd width) in a Horn row
                        let mut c = width_t;
                        while c >= 2 {
                            let (job, u) = unit(c - 2);
                            acc = b.horn2(acc, mu, [r[c - 1], r[c - 2]], job, u);
                            c -= 2;
                        }
                        while c > 0 {
                            c -= 1;
                            let (job, u) = unit(c);
                            acc = b.horn(acc, mu, r[c], job, u);
                        }
                    }
                    vals.push(acc);
                }
                for ct in 0..num_commits {
                    let leaf_digests: Vec<_> = if coset {
                        vec![ShaHasher.hash_coset(&rows[ct][qi])]
                    } else {
                        (0..(1 << k)).map(|j| ShaHasher.hash_slice(&rows[ct][qi][j])).collect()
                    };
                    pending[ct].push((job_bases[ct], leaf_digests, bits.clone(), index));
                }
                vals
            } else {
                let vs = &w.codeword_opened_values[round - 1][qi];
                let job_base = b.job_units.len() as u32;
                let coset = crate::sha384::config::sha_levers().coset_leaf;
                if coset {
                    b.job_start(crate::sha384::config::TAG_COSET_LEAF, 48 << k);
                } else {
                    for _ in 0..(1 << k) {
                        b.job_start(0, 48);
                    }
                }
                let vals: Vec<V> = vs
                    .iter()
                    .enumerate()
                    .map(|(j, &v)| {
                        let lv = b.load(v);
                        if coset {
                            b.unit12(lv, job_base, 2 + 12 * j as u32)
                        } else {
                            b.unit12(lv, job_base + j as u32, 2)
                        }
                    })
                    .collect();
                let rows_f: Vec<Vec<F>> = vs.iter().map(|v| v.as_basis_coefficients_slice().to_vec()).collect();
                let leaf_digests: Vec<_> = if coset {
                    vec![ShaHasher.hash_coset(&rows_f)]
                } else {
                    rows_f.iter().map(|r| ShaHasher.hash_slice(r)).collect()
                };
                pending[0].push((job_base, leaf_digests, bits.clone(), index));
                vals
            };
            // binary_k_fold(values, alphas_round, zi_root)
            let x = zi_root;
            let xinv_val = coeffs(x.val)[0].inverse();
            let xinv = b.load_f(xinv_val);
            let prod = b.mul(x, xinv);
            let one = b.c(F::ONE);
            b.assert_eq(prod, one, "zi_root inverse");
            let omega_k_inv = omega_k.inverse();
            let itw: Vec<F> = omega_k_inv.powers().take(1 << (k - 1)).collect();
            let xip = powers_of_2(b, xinv, k);
            let mut vals = values;
            let n = vals.len();
            // butterfly v_i + (alpha - t)(v_i - v_m) ti with t = x^(2^j) w^i, ti = x^(-2^j) w^-i / 2:
            // (alpha - t) ti = H_j w^-i - 1/2 with H_j = alpha x^(-2^j) / 2, so the new value is
            // v_m + G_i (v_i - v_m), G_i = H_j w^-i + 1/2  (5 rows instead of 7)
            for (j, &alpha) in alphas_round.iter().enumerate() {
                let mm = n >> (j + 1);
                let ax = b.mul(alpha, xip[j]);
                let h = b.mul_c(ax, F::ONE.halve());
                for i in 0..mm {
                    let g = if i == 0 { h } else { b.mul_c(h, itw[i << j]) };
                    let g = b.add_c(g, F::ONE.halve());
                    let d = b.sub(vals[i], vals[i + mm]);
                    let p = b.mul(g, d);
                    vals[i] = b.add(vals[i + mm], p);
                }
            }
            zs_round.push(zi);
            ys_round.push(vals[0]);
            qid += 1;
        }
        for (tree, pending) in pending.iter().enumerate() {
            let proofs = if is_initial { &w.initial_round_merkle_proofs[tree] } else { &w.codeword_merkle_proofs[round - 1] };
            let root = if is_initial { roots[tree] } else { round_commits[round - 1] };
            let depth = nbits + openvm_stark_backend::odd_domain::ceil_log2(odd);
            let siblings: Vec<Vec<crate::sha384::config::Digest>> = if multiproof {
                let leaves: Vec<_> = pending
                    .iter()
                    .map(|(_, ld, _, idx)| {
                        let mut layer = ld.clone();
                        while layer.len() > 1 {
                            layer = layer.chunks(2).map(|c| ShaHasher.compress(c[0], c[1])).collect();
                        }
                        (*idx, layer[0])
                    })
                    .collect();
                decompress_multiproof(&leaves, &proofs[0], depth, &mut b.failures)
            } else {
                proofs.clone()
            };
            for ((job_base, ld, bits, _), sib) in pending.iter().zip(&siblings) {
                assert_eq!(bits.len(), depth);
                b.merkle_path(*job_base, ld, sib, bits, &root);
            }
        }
        eprintln!(
            "NV_QCOST round={round} queries={nq} rows={} per_query={:.0} nbits={nbits} k={k} merkle_nodes={}",
            b.instrs.len() - q_start,
            (b.instrs.len() - q_start) as f64 / nq.max(1) as f64,
            b.merkle_nodes
        );
        // WHIR-Y lever: the shift-query answers are observed before gamma
        if params.whir.levers.whir_y {
            for &y in &ys_round {
                b.obs12(y);
            }
        }
        let gamma = b.smp12();
        if let Some(y0) = y0 {
            let t = b.mul(y0, gamma);
            claim = b.add(claim, t);
        }
        let mut gp = b.mul(gamma, gamma);
        for &y in &ys_round {
            let t = b.mul(y, gp);
            claim = b.add(claim, t);
            gp = b.mul(gp, gamma);
        }
        gammas.push(gamma);
        zs.push(zs_round);
        alphas.extend(alphas_round);
        log_rs -= shrink;
    }
    // final check
    let t = params.num_whir_sumcheck_rounds();
    let mut prefix = b.c(F::ONE);
    for i in 0..t {
        let w0 = {
            let z = b_zero(b);
            let d = b.dbl_add(u[i], z);
            b.one_minus(d)
        };
        let ox = b.one_minus(alphas[i]);
        let a = b.mul(w0, ox);
        let c = b.mul(u[i], alphas[i]);
        let f = b.add(a, c);
        prefix = b.mul(prefix, f);
    }
    // eval_mle_evals_at_point(final_poly, u[t..])
    let mut ev = final_poly.clone();
    let mut len = ev.len();
    for &xj in u[t..].iter().rev() {
        len >>= 1;
        let ox = b.one_minus(xj);
        for i in 0..len {
            let a = b.mul(ev[i], ox);
            let c = b.mul(ev[i + len], xj);
            ev[i] = b.add(a, c);
        }
    }
    let mut acc = b.mul(prefix, ev[0]);
    // eq(alpha_slc, y) = prod_m (1 - a_m) * prod_m (1 + y_m A_m), A_m = (2 a_m - 1) / (1 - a_m):
    // per-alpha factors and suffix products once, then 2 rows per variable per query point
    let (ainv, bsuf) = {
        let one = b.c(F::ONE);
        let mone = b.c(-F::ONE);
        let mut am = Vec::with_capacity(t);
        let mut bm = Vec::with_capacity(t);
        for &a in &alphas[..t] {
            let bb = b.one_minus(a);
            let bv = bb.val;
            let inv = b.load(if bv == EF::ZERO { EF::ZERO } else { bv.inverse() });
            if bv == EF::ZERO {
                b.failures.push("WHIR folding challenge alpha = 1 (eq factorisation)".into());
            }
            let pr = b.mul(bb, inv);
            b.assert_eq(pr, one, "eq factor inverse");
            let twoa = b.dbl_add(a, mone);
            am.push(b.mul(twoa, inv));
            bm.push(bb);
        }
        let mut suf = vec![one; t + 1];
        for m in (0..t).rev() {
            suf[m] = b.mul(bm[m], suf[m + 1]);
        }
        (am, suf)
    };
    let eq_fast = |b: &mut Builder, j: usize, y: &[V]| -> V {
        let mut e = bsuf[j];
        for (m, &ym) in y.iter().enumerate().take(t - j) {
            let p = b.mul(ym, ainv[j + m]);
            e = b.mul_add_a(e, p);
        }
        e
    };
    let mut j = params.whir.k_round(0);
    for i in 0..num_rounds {
        let gamma = gammas[i];
        let alpha_slc = &alphas[j..t];
        let slc_len = (t - j) + 1;
        if i != num_rounds - 1 {
            let zp = powers_of_2(b, z0s[i], slc_len);
            let (max, left) = zp.split_last().unwrap();
            debug_assert_eq!(alpha_slc.len(), left.len());
            let e = eq_fast(b, j, left);
            let h = b.horner_chain(&final_poly, *max);
            let t1 = b.mul(gamma, e);
            let t1 = b.mul(t1, h);
            acc = b.add(acc, t1);
        }
        let mut gp = b.mul(gamma, gamma);
        for &zi in &zs[i] {
            let zp = powers_of_2(b, zi, slc_len);
            let (max, left) = zp.split_last().unwrap();
            let e = eq_fast(b, j, left);
            let h = b.horner_chain(&final_poly, *max);
            let t1 = b.mul(gp, e);
            let t1 = b.mul(t1, h);
            acc = b.add(acc, t1);
            gp = b.mul(gp, gamma);
        }
        j += params.whir.k_round(i + 1);
    }
    b.assert_eq(acc, claim, "whir final");
}

#[allow(dead_code)]
fn _unused(_: &[EF]) {
    let _ = Itertools::collect_vec(std::iter::empty::<u8>());
}
