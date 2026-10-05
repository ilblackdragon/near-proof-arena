//! Honest prover for `np-udr-stark-v1` — low-memory version.
//!
//! Produces exactly the proofs of [`crate::prover_ref`] (tested bit for bit)
//! while keeping peak memory near the compact trace size:
//!
//! * the main trace is held as compact columns ([`TraceCols`]); aux columns
//!   are recomputed from it on demand; only quotient coefficients are stored;
//! * commitments stream column chunks into per-leaf SHA-256 states over
//!   groups of positions ([`crate::lmcommit`]); the lowest Merkle levels are
//!   recomputed at opening time;
//! * the quotient is evaluated pass by pass over ranges of LDE positions
//!   (current and next rows via [`eval_range`]), sized by the memory budget;
//! * OOD values and the DEEP combination are computed from values on `H`.
//!
//! Memory budget: `NPUDR_MEM_GB` (default 10).

use p3_dft::TwoAdicSubgroupDft;
use p3_field::{batch_multiplicative_inverse, BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::{log2_strict_usize, reverse_slice_index_bits};
use rayon::prelude::*;

use crate::air::{Air, Table, Tape};
use crate::aux::{aux_constraints, AuxLayout};
use crate::cols::TraceCols;
use crate::eval::BlockEval;
use crate::field::{ef_coeffs, ef_from_base, ef_from_coeffs, omega, shift, EF, F};
use crate::hash::{wh, Digest64, TAG_LEAF, TAG_NODE};
use crate::lmcommit::{self, CMat};
use crate::lmsrc::{AuxSrc, Src};
use crate::lowmem::{eval_range, Dft};
use crate::mmcs::{self, Opening, Tree};
use crate::protocol::{batch_coeffs, Proof, Schedule, LOG_BLOWUP, NUM_CHUNKS, PER_CHUNK};
use crate::transcript::Transcript;
use crate::verifier::{efs_bytes, global_checks, ood_offsets, public_inputs, Challenges};

pub use crate::prover_ref::ProveOptions;

/// Phase timer with the low-memory profiling counters.
pub struct Timer(crate::prover_ref::Timer);
impl Timer {
    fn new(on: bool) -> Self {
        Timer(crate::prover_ref::Timer::new(on))
    }
    fn lap(&mut self, what: &str) {
        let on = self.0.on;
        self.0.lap(what);
        if on {
            eprintln!("[prove]   {}", crate::lowmem::prof::report());
        }
    }
}

fn class_shift(k: usize) -> F {
    shift().exp_power_of_2(k)
}

fn xpow(l: usize) -> EF {
    EF::from_basis_coefficients_fn(|j| if j == l { F::ONE } else { F::ZERO })
}

fn ef_to_base_row(v: &[EF]) -> Vec<F> {
    let mut out = Vec::with_capacity(v.len() * 8);
    for x in v {
        out.extend_from_slice(ef_coeffs(x));
    }
    out
}

struct Budget {
    bytes: usize,
}

impl Budget {
    fn from_env() -> Budget {
        let gb: f64 = std::env::var("NPUDR_MEM_GB").ok().and_then(|v| v.parse().ok()).unwrap_or(11.0);
        Budget { bytes: (gb * (1u64 << 30) as f64) as usize }
    }
    /// column chunk for tables of `2^h` rows: three `T × chunk` buffers
    /// within 1/4 of the available bytes, at least 64 columns (≥ 256 bytes
    /// fed per leaf hash), at most 256
    fn chunk_for(&self, h: usize, used: usize) -> usize {
        let c = (self.avail(used) / 4) / (12usize << h);
        (c / 8 * 8).clamp(32, 256)
    }
    /// bytes available for transient buffers given `used` resident bytes
    /// (keeping room for chunk buffers and allocator slack)
    fn avail(&self, used: usize) -> usize {
        (self.bytes.saturating_sub(used) / 10 * 7).max(1 << 16)
    }
    /// level-0 positions hashed at once (128 bytes of state each), next to
    /// the chunk buffers
    fn group(&self, l0: usize, used: usize, chunk_bytes: usize) -> usize {
        let a = self.avail(used).saturating_sub(chunk_bytes).max(1 << 16);
        let mut s = 1usize << l0;
        while s > 1 << 12 && s * 128 > a {
            s /= 2;
        }
        s
    }
}

/// `Σ_r wts[r] · m[r][c]` for every column `c`.
fn dot_rows(m: &RowMajorMatrix<F>, wts: &[EF]) -> Vec<EF> {
    let t = m.height();
    let w = m.width();
    let ch = (t / (4 * rayon::current_num_threads().max(1))).max(256);
    (0..t.div_ceil(ch))
        .into_par_iter()
        .map(|k| {
            let mut acc = vec![EF::ZERO; w];
            for r in k * ch..((k + 1) * ch).min(t) {
                let row = &m.values[r * w..(r + 1) * w];
                let wr = wts[r];
                for c in 0..w {
                    acc[c] += wr * row[c];
                }
            }
            acc
        })
        .reduce(
            || vec![EF::ZERO; w],
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(b) {
                    *x += y;
                }
                a
            },
        )
}

/// Barycentric weights: `f(ζ) = Σ_r wts[r]·f(ω^r)` on `H = ⟨ω_T⟩`.
fn bary_weights(h: usize, zeta: EF) -> Vec<EF> {
    let t = 1usize << h;
    let pts: Vec<F> = omega(h).powers().take(t).collect();
    let den: Vec<EF> = pts.iter().map(|&p| zeta - ef_from_base(p)).collect();
    let inv = batch_multiplicative_inverse(&den);
    let scale = (zeta.exp_power_of_2(h) - EF::ONE) * ef_from_base(F::from_u64(t as u64).inverse());
    inv.iter().zip(&pts).map(|(i, &p)| *i * p * scale).collect()
}

/// `out[r] += Σ_k coef[k]·c[r][k]`.
fn combine_into(out: &mut [EF], c: &RowMajorMatrix<F>, coef: &[EF]) {
    let w = c.width();
    out.par_iter_mut().enumerate().for_each(|(r, o)| {
        let row = &c.values[r * w..(r + 1) * w];
        let mut acc = EF::ZERO;
        for k in 0..w {
            acc += coef[k] * row[k];
        }
        *o += acc;
    });
}

struct QCtx<'a> {
    tab: &'a Table,
    lay: &'a AuxLayout,
    alpha_fp: EF,
    gamma: EF,
    alpha_c: EF,
    fins: &'a [EF],
    pubs: &'a [F],
}

/// Column polynomials of one table held as coefficient chunks (`T × cw`
/// each; chunk `i` holds columns `c0_i .. c0_i + cw_i`).
struct Coefs {
    width: usize,
    parts: Vec<(usize, RowMajorMatrix<F>)>,
}

impl Coefs {
    fn new() -> Self {
        Coefs { width: 0, parts: vec![] }
    }
    /// Append columns given by their values on `H` (natural order).
    fn push_values(&mut self, dft: &Dft, vals: RowMajorMatrix<F>) {
        let w = vals.width();
        if w == 0 {
            return;
        }
        let _t = std::time::Instant::now();
        let c = dft.idft_batch(vals);
        crate::lowmem::prof::add(&crate::lowmem::prof::COEFFS, _t);
        self.parts.push((self.width, c));
        self.width += w;
    }
    fn bytes(&self) -> usize {
        self.parts.iter().map(|(_, m)| m.values.len() * 4).sum()
    }
    /// Evaluations at LDE positions `p0 .. p0+len` (`len ≤ T`, aligned) into
    /// the row-major `len × width` buffer `dst`.
    fn eval_into(&self, dft: &Dft, lde: usize, sh: F, p0: usize, len: usize, dst: &mut [F]) {
        let _t = std::time::Instant::now();
        let width = self.width;
        for (c0, co) in &self.parts {
            let cw = co.width();
            let ev = eval_range(dft, co, lde, sh, p0, len, None);
            let c0 = *c0;
            dst.par_chunks_mut(width * 1024).enumerate().for_each(|(k, rows)| {
                for (i, row) in rows.chunks_mut(width).enumerate() {
                    let r = k * 1024 + i;
                    row[c0..c0 + cw].copy_from_slice(&ev.values[r * cw..(r + 1) * cw]);
                }
            });
        }
        crate::lowmem::prof::add(&crate::lowmem::prof::FILL, _t);
    }
}

/// Rows of a [`Coefs`] on LDE ranges, in one of two halves (`2·len × width`)
/// so that the next rows of one range can be the current rows of the next.
struct Halves {
    width: usize,
    len: usize,
    buf: Vec<F>,
}

impl Halves {
    fn new(width: usize, len: usize, halves: usize) -> Self {
        Halves { width, len, buf: vec![F::ZERO; halves * len * width] }
    }
    fn load(&mut self, set: &Coefs, dft: &Dft, half: usize, p0: usize, lde: usize, sh: F) {
        let (w, len) = (self.width, self.len);
        set.eval_into(dft, lde, sh, p0, len, &mut self.buf[half * len * w..(half + 1) * len * w]);
    }
}
fn pass_len(per_pt: usize, avail: usize, npts: usize) -> usize {
    let mut pass = npts.next_power_of_two();
    while pass > 1024 && pass * per_pt > avail {
        pass /= 2;
    }
    pass.min(npts)
}

/// The evaluation schedule of one quotient pass family: ranges of `len`
/// positions of the first `npts` LDE positions, each paired with the range
/// holding its next rows.
///
/// * `len ≥ T`: whole blocks; the next row of block position `u` is block
///   position `rev(rev(u)+1)` (same half).
/// * `len < T`: block `b` splits into `2^s` ranges; range `j` holds natural
///   residue `a = rev_s(j)` mod `2^s`; the next rows of residue `a` are the
///   same offsets of residue `a+1`, and of the last residue the offsets
///   `rev(rev(v)+1)` of residue 0. Ranges are visited in residue order, each
///   evaluated once (residue 0 twice per block).
struct Step {
    /// positions of the current range
    p0: usize,
    /// half holding the current rows
    cur: usize,
    /// load into the other half before evaluating: `Some(p0)` of the next rows
    load_next: Option<usize>,
    /// next-row index of offset `v`: `None` = same offset in the other half,
    /// `Some(perm)` = permuted offsets (in the half given by `next_half`)
    perm: bool,
    next_half: usize,
}

fn schedule(npts: usize, t: usize, h: usize, len: usize) -> Vec<(Option<usize>, Step)> {
    // (load_cur, step): load_cur = Some(p0) when the current range must be loaded first
    let mut v = vec![];
    if len >= t {
        for p0 in (0..npts).step_by(len) {
            v.push((Some(p0), Step { p0, cur: 0, load_next: None, perm: true, next_half: 0 }));
        }
        return v;
    }
    let s = p3_util::log2_strict_usize(t / len);
    for b in 0..npts / t {
        let pos = |a: usize| b * t + crate::mmcs::rev(a, s) * len;
        let mut cur = 0;
        for a in 0..1usize << s {
            let last = a + 1 == 1 << s;
            let nxt = if last { pos(0) } else { pos(a + 1) };
            let load_cur = if a == 0 { Some(pos(0)) } else { None };
            v.push((load_cur, Step { p0: pos(a), cur, load_next: Some(nxt), perm: last, next_half: 1 - cur }));
            cur = 1 - cur;
        }
    }
    let _ = h;
    v
}

/// Next-row indices into a two-half buffer for one step.
fn next_index(st: &Step, len: usize, t: usize, h: usize) -> Vec<u32> {
    let base = (st.next_half * len) as u32;
    if !st.perm {
        return (0..len as u32).map(|v| base + v).collect();
    }
    if len >= t {
        // whole blocks: rotation inside each block
        (0..len)
            .map(|u| {
                let b = u / t;
                let w = u % t;
                base + (b * t + crate::mmcs::rev((crate::mmcs::rev(w, h) + 1) % t, h)) as u32
            })
            .collect()
    } else {
        let bits = p3_util::log2_strict_usize(len);
        (0..len).map(|v| base + crate::mmcs::rev((crate::mmcs::rev(v, bits) + 1) % len, bits) as u32).collect()
    }
}

/// `V⁻¹` for the Vandermonde matrix `V[b][m] = z_b^m` (`n × n`, distinct
/// nodes), as `W[m][b]`.
fn vandermonde_inverse(z: &[F]) -> Vec<Vec<F>> {
    let n = z.len();
    // Gauss–Jordan on [V | I]
    let mut a: Vec<Vec<F>> = (0..n)
        .map(|b| {
            let mut row: Vec<F> = z[b].powers().take(n).collect();
            row.extend((0..n).map(|j| if j == b { F::ONE } else { F::ZERO }));
            row
        })
        .collect();
    for col in 0..n {
        let piv = (col..n).find(|&r| !a[r][col].is_zero()).expect("distinct nodes");
        a.swap(col, piv);
        let inv = a[col][col].inverse();
        for x in a[col].iter_mut() {
            *x *= inv;
        }
        for r in 0..n {
            if r != col && !a[r][col].is_zero() {
                let f = a[r][col];
                let pr = a[col].clone();
                for (x, p) in a[r].iter_mut().zip(pr) {
                    *x -= f * p;
                }
            }
        }
    }
    // rows of V⁻¹ are indexed by m
    (0..n).map(|m| a[m][n..].to_vec()).collect()
}

/// Lagrange selectors `L_0`, `L_{T-1}` at LDE positions `p0..p0+len`.
fn selectors(h: usize, lde: usize, sh: F, p0: usize, len: usize) -> (Vec<F>, Vec<F>) {
    let a = log2_strict_usize(len);
    let c = sh * omega(lde).exp_u64(crate::mmcs::rev(p0 >> a, lde - a) as u64);
    let mut xs: Vec<F> = omega(a).shifted_powers(c).take(len).collect();
    reverse_slice_index_bits(&mut xs);
    let tf = F::from_u64(1u64 << h);
    let h_last = omega(h).inverse();
    let zs: Vec<F> = xs.iter().map(|&x| x.exp_power_of_2(h) - F::ONE).collect();
    let i1 = batch_multiplicative_inverse(&xs.iter().map(|&x| tf * (x - F::ONE)).collect::<Vec<_>>());
    let i2 = batch_multiplicative_inverse(&xs.iter().map(|&x| tf * (x - h_last)).collect::<Vec<_>>());
    ((0..len).map(|i| zs[i] * i1[i]).collect(), (0..len).map(|i| h_last * zs[i] * i2[i]).collect())
}

/// Quotient of one table as chunk coefficients (`T × 8·nq`, row `j`:
/// coefficient `j` of chunks `0..nq`).
///
/// `Q = Σ_m X^{mT}·Q_m` has degree `< nq·T`, so its values on `nq` cosets
/// `c_b·H` (LDE blocks `b < nq`, whose `z_b = c_b^T` are distinct) determine
/// it: on block `b`, `Q(c_b·X) ≡ Σ_m z_b^m·Q_m(c_b·X) mod X^T − 1`, so the
/// coset iDFT of the block gives `y_b = Σ_m z_b^m·q_m` coefficient-wise and
/// `q = V⁻¹·y`. The zerofier is the constant `z_b − 1` on block `b`.
///
/// Bus constraints are evaluated first (aux columns and interaction values
/// as cached coefficients), then the main constraints with the table's
/// trace converted to coefficients in place (its compact columns are
/// released meanwhile and rebuilt afterwards). Positions are processed in
/// ranges sized by the memory budget.
#[allow(clippy::too_many_arguments)]
fn quotient(
    dft: &Dft,
    tape: &Tape,
    trace: &mut TraceCols,
    h: usize,
    class: usize,
    nq: usize,
    q: &QCtx,
    bud: &Budget,
    used: usize,
    chunk: usize,
) -> Result<RowMajorMatrix<F>, String> {
    let t = 1usize << h;
    if nq == 0 || nq > 1 << LOG_BLOWUP {
        return Err(format!("unsupported quotient chunk count {nq}"));
    }
    let npts = nq * t;
    let lde = h + LOG_BLOWUP;
    let sh = class_shift(class);
    let apow: Vec<EF> = q.alpha_c.powers().take(tape.outputs.len()).collect();
    let a_aux = q.alpha_c.exp_u64(tape.outputs.len() as u64);
    let w = trace.width();
    let wa = q.lay.width();
    let aw = 8 * wa;
    let beval = BlockEval::new(tape, q.pubs);
    // resident besides this table's compact trace, plus the accumulator
    let used = used.saturating_sub(trace.bytes()) + npts * 32;
    let mut qv = vec![EF::ZERO; npts];
    const CH: usize = 1024;

    // ---- family 1: bus constraints ----
    if wa > 0 {
        let asrc = AuxSrc::new(trace, q.tab, q.lay, q.pubs, q.alpha_fp, q.gamma);
        let mut ac = Coefs::new();
        let step = (chunk / 8).max(1) * 8;
        for c0 in (0..aw).step_by(step) {
            ac.push_values(dft, asrc.values(c0, (c0 + step).min(aw)));
        }
        // interaction values: the expressions themselves (degree ≤ 1) when
        // fewer than the columns they read, else those columns
        let nout = q.lay.itape.outputs.len();
        let use_ivals = nout < asrc.cols.len();
        let mut ic = Coefs::new();
        if use_ivals {
            for o0 in (0..nout).step_by(chunk) {
                ic.push_values(dft, asrc.ivals(o0, (o0 + chunk).min(nout)));
            }
        } else {
            for l in asrc.cols.chunks(chunk) {
                ic.push_values(dft, cols_values(trace, l));
            }
        }
        let iw = ic.width;
        let mut map = vec![u32::MAX; w];
        for (j, &c) in asrc.cols.iter().enumerate() {
            map[c] = j as u32;
        }
        let fast = FastBus::new(q, a_aux);
        let ihalves = if use_ivals { 1 } else { 2 };
        let avail = bud.avail(used + trace.bytes() + ac.bytes() + ic.bytes());
        let len = pass_len((2 * aw + ihalves * iw) * 4 + 48, avail, t);
        let mut ha = Halves::new(aw, len, 2);
        let mut hi = Halves::new(iw, len, ihalves);
        for (load_cur, st) in schedule(npts, t, h, len) {
            if let Some(p) = load_cur {
                ha.load(&ac, dft, st.cur, p, lde, sh);
                if !use_ivals {
                    hi.load(&ic, dft, st.cur, p, lde, sh);
                }
            }
            if let Some(p) = st.load_next {
                ha.load(&ac, dft, 1 - st.cur, p, lde, sh);
                if !use_ivals {
                    hi.load(&ic, dft, 1 - st.cur, p, lde, sh);
                }
            }
            if use_ivals {
                hi.load(&ic, dft, 0, st.p0, lde, sh);
            }
            let (sfirst, slast) = selectors(h, lde, sh, st.p0, len);
            let next32 = next_index(&st, len, t, h);
            let ta0 = std::time::Instant::now();
            let (ibuf, abuf) = (&hi.buf, &ha.buf);
            let row0 = st.cur * len;
            let irow0 = if use_ivals { 0 } else { row0 };
            qv[st.p0..st.p0 + len].par_iter_mut().enumerate().for_each_init(
                || (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new()),
                |(iregs, cs, phis, ivals, av, anv, ivb), (u, acc)| {
                    let sel = [sfirst[u], slast[u], F::ONE - slast[u]];
                    let ru = row0 + u;
                    let nu = next32[u] as usize;
                    if let Some(fb) = &fast {
                        let iv: &[F] = if use_ivals {
                            let iu = irow0 + u;
                            &ibuf[iu * iw..(iu + 1) * iw]
                        } else {
                            let row = &ibuf[ru * iw..(ru + 1) * iw];
                            let nrow = &ibuf[nu * iw..(nu + 1) * iw];
                            let col = |c: usize, nn: bool| {
                                let j = map[c] as usize;
                                if nn { nrow[j] } else { row[j] }
                            };
                            q.lay.itape.eval::<F>(iregs, col, q.pubs, sel);
                            ivb.clear();
                            ivb.extend(q.lay.itape.outputs.iter().map(|&o| iregs[o as usize]));
                            ivb
                        };
                        let ar = &abuf[ru * aw..(ru + 1) * aw];
                        let an = &abuf[nu * aw..(nu + 1) * aw];
                        av.clear();
                        av.extend((0..wa).map(|c| ef_from_coeffs(&ar[8 * c..8 * c + 8])));
                        anv.clear();
                        anv.extend((0..wa).map(|c| ef_from_coeffs(&an[8 * c..8 * c + 8])));
                        *acc += fb.eval(iv, av, anv, sel, q.fins, phis);
                        return;
                    }
                    ivals.clear();
                    if use_ivals {
                        let iu = irow0 + u;
                        ivals.extend(ibuf[iu * iw..(iu + 1) * iw].iter().map(|&x| ef_from_base(x)));
                    } else {
                        let row = &ibuf[ru * iw..(ru + 1) * iw];
                        let nrow = &ibuf[nu * iw..(nu + 1) * iw];
                        let col = |c: usize, nn: bool| {
                            let j = map[c] as usize;
                            if nn { nrow[j] } else { row[j] }
                        };
                        q.lay.itape.eval::<F>(iregs, col, q.pubs, sel);
                        ivals.extend(q.lay.itape.outputs.iter().map(|&o| ef_from_base(iregs[o as usize])));
                    }
                    let ar = &abuf[ru * aw..(ru + 1) * aw];
                    let an = &abuf[nu * aw..(nu + 1) * aw];
                    av.clear();
                    av.extend((0..wa).map(|c| ef_from_coeffs(&ar[8 * c..8 * c + 8])));
                    anv.clear();
                    anv.extend((0..wa).map(|c| ef_from_coeffs(&an[8 * c..8 * c + 8])));
                    cs.clear();
                    aux_constraints(q.tab, q.lay, ivals, q.alpha_fp, q.gamma, av, anv, q.fins, sel.map(ef_from_base), cs, phis);
                    let mut pw = a_aux;
                    for c in cs.iter() {
                        *acc += pw * *c;
                        pw *= q.alpha_c;
                    }
                },
            );
            crate::lowmem::prof::add(&crate::lowmem::prof::AUXC, ta0);
        }
    }

    // ---- family 2: main constraints, trace converted to coefficients ----
    let mut mc = Coefs::new();
    for c0 in (0..w).step_by(chunk) {
        let v = trace.take_chunk(c0, (c0 + chunk).min(w));
        mc.push_values(dft, v);
    }
    let avail = bud.avail(used + trace.bytes() + mc.bytes());
    let len = pass_len(2 * w * 4 + 48, avail, t);
    let mut hm = Halves::new(w, len, 2);
    for (load_cur, st) in schedule(npts, t, h, len) {
        if let Some(p) = load_cur {
            hm.load(&mc, dft, st.cur, p, lde, sh);
        }
        if let Some(p) = st.load_next {
            hm.load(&mc, dft, 1 - st.cur, p, lde, sh);
        }
        let (sfirst, slast) = selectors(h, lde, sh, st.p0, len);
        let next32 = next_index(&st, len, t, h);
        let tb0 = std::time::Instant::now();
        let row0 = st.cur * len;
        // `eval_rows` overwrites its output: evaluate aside, then add to
        // the bus-constraint part already accumulated
        qv[st.p0..st.p0 + len].par_chunks_mut(CH).enumerate().for_each_init(Vec::new, |tmp, (ci, o)| {
            let r0 = ci * CH;
            let r1 = r0 + o.len();
            tmp.clear();
            tmp.resize(o.len(), EF::ZERO);
            beval.eval_rows(&hm.buf, w, row0 + r0, &next32[r0..r1], &sfirst[r0..r1], &slast[r0..r1], &apow, tmp);
            for (x, y) in o.iter_mut().zip(tmp.iter()) {
                *x += *y;
            }
        });
        crate::lowmem::prof::add(&crate::lowmem::prof::BEVAL, tb0);
    }
    drop(hm);
    // rebuild the compact trace from the coefficients
    let _tr = std::time::Instant::now();
    for (c0, co) in std::mem::take(&mut mc.parts) {
        let v = dft.dft_batch(co).to_row_major_matrix();
        trace.put_chunk(c0, &v);
    }
    crate::lowmem::prof::add(&crate::lowmem::prof::COEFFS, _tr);

    // ---- interpolation: q = V⁻¹·y ----
    let zb: Vec<(F, F)> = (0..nq)
        .map(|b| {
            let c = sh * omega(lde).exp_u64(crate::mmcs::rev(b * t, lde) as u64);
            (c, c.exp_power_of_2(h))
        })
        .collect();
    let winv = vandermonde_inverse(&zb.iter().map(|x| x.1).collect::<Vec<_>>());
    let wq = 8 * nq;
    let mut out = RowMajorMatrix::new(vec![F::ZERO; t * wq], wq);
    for (b, &(c, z)) in zb.iter().enumerate() {
        let blk = &mut qv[b * t..(b + 1) * t];
        let zi = (z - F::ONE).inverse();
        blk.par_iter_mut().for_each(|x| *x *= zi);
        reverse_slice_index_bits(blk);
        let y = dft.coset_idft_batch(RowMajorMatrix::new(ef_to_base_row(blk), 8), c);
        let wb: Vec<F> = (0..nq).map(|m| winv[m][b]).collect();
        out.values.par_chunks_mut(wq).zip(y.values.par_chunks(8)).for_each(|(o, yr)| {
            for (m, &wm) in wb.iter().enumerate() {
                for l in 0..8 {
                    o[8 * m + l] += wm * yr[l];
                }
            }
        });
    }
    Ok(out)
}

/// Bus constraints at one point for tables whose interactions have at most
/// one multiplicity bit (no chain columns): the same accumulated value as
/// `Σ_c a_aux·α_c^c·C_c` over [`aux_constraints`]' outputs, computed with
/// base-field interaction values (fingerprints as `Σ α^k·msg_k`).
struct FastBus {
    /// per interaction: offset in the itape outputs, message length,
    /// multiplicity-bit count, `α^0..α^len`, `(bus+1)·α^len`
    inter: Vec<(usize, usize, usize, Vec<EF>, EF)>,
    groups: Vec<Vec<usize>>,
    /// per group: weights of its three constraints
    wts: Vec<[EF; 3]>,
    gamma: EF,
}

impl FastBus {
    fn new(q: &QCtx, a_aux: EF) -> Option<FastBus> {
        if q.lay.n_chain != 0 || q.tab.interactions.iter().any(|i| i.mult.len() > 1) {
            return None;
        }
        let inter = q
            .tab
            .interactions
            .iter()
            .enumerate()
            .map(|(ii, it)| {
                let ap: Vec<EF> = q.alpha_fp.powers().take(it.msg.len() + 1).collect();
                let last = ap[it.msg.len()] * F::from_u64(it.bus as u64 + 1);
                (q.lay.expr_off[ii], it.msg.len(), it.mult.len(), ap, last)
            })
            .collect();
        let mut pw = a_aux;
        let wts = (0..q.lay.groups.len())
            .map(|_| {
                let w = [pw, pw * q.alpha_c, pw * q.alpha_c * q.alpha_c];
                pw = w[2] * q.alpha_c;
                w
            })
            .collect();
        Some(FastBus { inter, groups: q.lay.groups.clone(), wts, gamma: q.gamma })
    }
    /// `iv`: itape outputs (base field); `phis`: scratch.
    #[inline]
    fn eval(&self, iv: &[F], av: &[EF], anv: &[EF], sel: [F; 3], fins: &[EF], phis: &mut Vec<EF>) -> EF {
        phis.clear();
        for (o, len, k, ap, last) in &self.inter {
            if *k == 0 {
                phis.push(EF::ONE);
                continue;
            }
            let mut fp = *last;
            for j in 0..*len {
                fp += ap[j] * iv[o + j];
            }
            phis.push(EF::ONE + (self.gamma - fp - EF::ONE) * iv[o + len]);
        }
        let mut acc = EF::ZERO;
        for (g, grp) in self.groups.iter().enumerate() {
            let mut phi = EF::ONE;
            for &i in grp {
                phi *= phis[i];
            }
            let a = av[g];
            let ap = a * phi;
            let w = &self.wts[g];
            acc += w[0] * ((a - EF::ONE) * sel[0]) + w[1] * ((anv[g] - ap) * sel[2]) + w[2] * ((ap - fins[g]) * sel[1]);
        }
        acc
    }
}

/// Values on `H` of the main-trace columns `list`.
fn cols_values(trace: &TraceCols, list: &[usize]) -> RowMajorMatrix<F> {
    let w = list.len();
    let h = trace.height();
    let mut v = vec![F::ZERO; h * w];
    v.par_chunks_mut(w.max(1) * 1024).enumerate().for_each(|(k, rows)| {
        for (i, row) in rows.chunks_mut(w.max(1)).enumerate() {
            let r = k * 1024 + i;
            for (j, &c) in list.iter().enumerate() {
                row[j] = trace.get(r, c);
            }
        }
    });
    RowMajorMatrix::new(v, w)
}
/// FRI layer commitment from the evaluation vector (leaf `j` = positions
/// `j·2^a .. (j+1)·2^a`), without copying it.
fn fri_commit(f: &[EF], a: usize) -> Tree {
    let ar = 1usize << a;
    let n = f.len() / ar;
    let l0 = log2_strict_usize(n);
    let lvl0: Vec<Digest64> = (0..n)
        .into_par_iter()
        .map_init(Vec::new, |buf, j| {
            buf.clear();
            for x in &f[j * ar..(j + 1) * ar] {
                for c in ef_coeffs(x) {
                    buf.extend_from_slice(&c.as_canonical_u32().to_le_bytes());
                }
            }
            wh(TAG_LEAF, &[buf])
        })
        .collect();
    let mut levels = vec![lvl0];
    for k in 1..=l0 {
        let prev = &levels[k - 1];
        let lvl: Vec<Digest64> =
            (0..prev.len() / 2).into_par_iter().map(|j| wh(TAG_NODE, &[&[k as u8], &prev[2 * j], &prev[2 * j + 1]])).collect();
        levels.push(lvl);
    }
    Tree { log_h0: l0, levels }
}

fn fri_open(f: &[EF], a: usize, tree: &Tree, idx: &[usize]) -> Opening {
    let ar = 1usize << a;
    let sets = mmcs::index_sets(tree.log_h0, idx);
    let mut rows = vec![];
    for &j in &sets[0] {
        rows.extend(ef_to_base_row(&f[j * ar..(j + 1) * ar]));
    }
    Opening { rows: vec![rows], siblings: mmcs::siblings(tree, idx) }
}

fn cmats<'a>(sch: &Schedule, srcs: &'a [Src<'a>]) -> Vec<CMat<'a>> {
    (0..sch.num_tables())
        .map(|t| CMat { src: &srcs[t], lde: sch.log_lde(t), shift: class_shift(sch.class[t]), class: sch.class[t] })
        .collect()
}

/// Prove from row-major traces (converted to compact columns first).
pub fn prove(
    air: &Air,
    traces: Vec<RowMajorMatrix<F>>,
    pub_tape: &[u8],
    cb: &[u8],
    opts: &ProveOptions,
) -> Result<(Proof, Schedule, Vec<usize>), String> {
    for (t, tr) in traces.iter().enumerate() {
        if t < air.tables.len() && (tr.width() != air.tables[t].width || !tr.height().is_power_of_two()) {
            return Err(format!("table {t}: bad trace shape"));
        }
    }
    let cols: Vec<TraceCols> = traces.iter().map(TraceCols::from_matrix).collect();
    drop(traces);
    prove_cols(air, cols, pub_tape, cb, opts)
}

pub fn prove_cols(
    air: &Air,
    traces: Vec<TraceCols>,
    pub_tape: &[u8],
    cb: &[u8],
    opts: &ProveOptions,
) -> Result<(Proof, Schedule, Vec<usize>), String> {
    let mut tm = Timer::new(opts.verbose);
    air.validate()?;
    if traces.len() != air.tables.len() {
        return Err("trace count".into());
    }
    for (t, tr) in traces.iter().enumerate() {
        if tr.width() != air.tables[t].width {
            return Err(format!("table {t}: bad trace shape"));
        }
    }
    let heights: Vec<usize> = traces.iter().map(|m| m.log_h).collect();
    let sch = Schedule::new(air, &heights)?;
    let nt = sch.num_tables();
    let l0 = sch.l0;
    let pubs = public_inputs(air, cb);
    let dft = Dft::default();
    let bud = Budget::from_env();
    // resident: compact traces, two stored trees (levels ≥ KEEP), quotient coefficients
    let tree_bytes = (64usize << l0) >> (crate::lmcommit::KEEP - 1);
    let mut resident = traces.iter().map(|t| t.bytes()).sum::<usize>() + 2 * tree_bytes;
    for t in 0..nt {
        resident += (8 * sch.n_quot[t] * 4) << heights[t];
    }
    let hmax0 = *heights.iter().max().unwrap();
    let chunk = bud.chunk_for(hmax0, resident);
    let group = bud.group(l0, resident, (12 * chunk) << hmax0);
    if opts.verbose {
        eprintln!("[prove] resident {} MB, chunk {chunk}, group 2^{}", resident >> 20, log2_strict_usize(group));
    }
    let mut tr = Transcript::new(pub_tape, cb);
    let lays: Vec<AuxLayout> = air.tables.iter().map(AuxLayout::new).collect();

    let mut traces = traces;
    // ---- message 0: header ‖ main commitment ----
    let compact = traces.iter().map(|t| t.bytes()).sum::<usize>();
    let main_tree = {
        let main: Vec<Src> = traces.iter().map(Src::Main).collect();
        // only the compact traces are resident yet
        let g = bud.group(l0, compact, (12 * chunk) << hmax0);
        if opts.verbose {
            eprintln!("[prove] main commit group 2^{}", log2_strict_usize(g));
        }
        lmcommit::commit(&dft, &cmats(&sch, &main), l0, g, chunk)
    };
    tm.lap("main commit");
    tr.absorb(&[main_tree.root()], &sch.header_bytes());
    let alpha_fp = tr.chal();
    let gamma = tr.chal();

    // ---- message 2: aux (grand products) ‖ finals ----
    fn aux_srcs<'a>(traces: &'a [TraceCols], air: &'a Air, lays: &'a [AuxLayout], pubs: &'a [F], a: EF, g: EF) -> Vec<AuxSrc<'a>> {
        (0..traces.len()).map(|t| AuxSrc::new(&traces[t], &air.tables[t], &lays[t], pubs, a, g)).collect()
    }
    let (aux_tree, aux_finals) = {
        let srcs = aux_srcs(&traces, air, &lays, &pubs, alpha_fp, gamma);
        let mut aux_finals = vec![];
        for a in &srcs {
            aux_finals.extend(a.finals());
        }
        // aux coefficients computed once (not once per position group), when
        // they fit next to the compact traces
        let cache: usize = (0..nt).map(|t| (8 * sch.w_aux[t] * 4) << heights[t]).sum();
        let use_cache = compact + tree_bytes + cache <= bud.bytes / 4 * 3;
        let aux: Vec<Src> = srcs
            .into_iter()
            .map(|a| {
                let s = Src::Aux(a);
                let w = s.width();
                if w == 0 || !use_cache {
                    return s;
                }
                let parts = s.chunks(chunk).into_iter().map(|(c0, c1)| (c0, s.coeffs(&dft, c0, c1))).collect();
                Src::Chunks(parts, w)
            })
            .collect();
        let used = compact + tree_bytes + if use_cache { cache } else { 0 };
        let g = bud.group(l0, used, (12 * chunk) << hmax0);
        if opts.verbose {
            eprintln!("[prove] aux coefficient cache {} MB ({use_cache}), group 2^{}", cache >> 20, log2_strict_usize(g));
        }
        (lmcommit::commit(&dft, &cmats(&sch, &aux), l0, g, chunk), aux_finals)
    };
    tr.absorb(&[aux_tree.root()], &efs_bytes(&aux_finals));
    let alpha_c = tr.chal();
    tm.lap("aux");

    // ---- message 3: quotient ----
    let tapes: Vec<Tape> = air.tables.iter().map(|t| Tape::compile(&t.constraints)).collect();
    let mut foffs = vec![0usize; nt + 1];
    for t in 0..nt {
        foffs[t + 1] = foffs[t] + sch.n_finals[t];
    }
    // largest tables first, while the fewest quotients are resident
    let mut order: Vec<usize> = (0..nt).collect();
    order.sort_by_key(|&t| std::cmp::Reverse(traces[t].bytes()));
    let mut quot_c: Vec<Option<RowMajorMatrix<F>>> = (0..nt).map(|_| None).collect();
    // resident now: compact traces, two stored trees, finished quotients
    let mut qres = compact + 2 * tree_bytes;
    for &t in &order {
        let fins = &aux_finals[foffs[t]..foffs[t + 1]];
        let q = QCtx { tab: &air.tables[t], lay: &lays[t], alpha_fp, gamma, alpha_c, fins, pubs: &pubs };
        let qc = quotient(&dft, &tapes[t], &mut traces[t], heights[t], sch.class[t], sch.n_quot[t], &q, &bud, qres, chunk)
            .map_err(|e| format!("table {t}: {e}"))?;
        qres += qc.values.len() * 4;
        quot_c[t] = Some(qc);
    }
    let quot: Vec<Src> = quot_c.into_iter().map(|q| Src::Coeffs(q.unwrap())).collect();
    tm.lap("quotient");
    let main: Vec<Src> = traces.iter().map(Src::Main).collect();
    let main_m = cmats(&sch, &main);
    let aux: Vec<Src> = aux_srcs(&traces, air, &lays, &pubs, alpha_fp, gamma).into_iter().map(Src::Aux).collect();
    let aux_m = cmats(&sch, &aux);
    let quot_m = cmats(&sch, &quot);
    let quot_tree = lmcommit::commit(&dft, &quot_m, l0, group, chunk);
    tm.lap("quot commit");
    tr.absorb(&[quot_tree.root()], &[]);
    let z = tr.chal_ood();

    // ---- message 4: OOD values ----
    let kvals = |v: Vec<EF>, n: usize| -> Vec<EF> {
        (0..n).map(|m| (0..8).fold(EF::ZERO, |acc, l| acc + xpow(l) * v[8 * m + l])).collect()
    };
    let mut ood = vec![];
    for t in 0..nt {
        let h = heights[t];
        let gz = z * ef_from_base(omega(h));
        let (wz, wg) = (bary_weights(h, z), bary_weights(h, gz));
        let ck = chunk;
        let (mut vz, mut vg) = (vec![], vec![]);
        for (c0, c1) in main[t].chunks(ck) {
            let v = main[t].values(&dft, c0, c1);
            vz.extend(dot_rows(&v, &wz));
            vg.extend(dot_rows(&v, &wg));
        }
        ood.extend(vz);
        ood.extend(vg);
        let wa = sch.w_aux[t];
        if wa > 0 {
            let (mut az, mut ag) = (vec![], vec![]);
            for (c0, c1) in aux[t].chunks(ck) {
                let v = aux[t].values(&dft, c0, c1);
                az.extend(dot_rows(&v, &wz));
                ag.extend(dot_rows(&v, &wg));
            }
            ood.extend(kvals(az, wa));
            ood.extend(kvals(ag, wa));
        }
        if let Src::Coeffs(qc) = &quot[t] {
            let zp: Vec<EF> = z.powers().take(qc.height()).collect();
            ood.extend(kvals(dot_rows(qc, &zp), sch.n_quot[t]));
        }
    }
    tm.lap("ood");
    let pre = Challenges { alpha_fp, gamma_mul: gamma, alpha_c, z, batch: vec![], beta: vec![], gamma_roll: vec![], queries: vec![] };
    global_checks(air, &sch, &ood, &aux_finals, &pre, &pubs).map_err(|e| format!("{e}: the trace does not satisfy the AIR"))?;
    tr.absorb(&[], &efs_bytes(&ood));
    let batch: Vec<EF> = (0..sch.batch_rounds).map(|_| tr.chal()).collect();

    // ---- DEEP batches per class layer (bit-reversed order) ----
    let ood_off = ood_offsets(&sch);
    let mut deep: Vec<Vec<EF>> = vec![];
    for (ci, &c) in sch.class_layers.iter().enumerate() {
        let lg = l0 - c;
        let n = 1usize << lg;
        let ts = sch.tables_of(c);
        let h = heights[ts[0]];
        let t_rows = 1usize << h;
        let coeffs = batch_coeffs(&batch, sch.batch_len[ci]);
        let gz = z * ef_from_base(omega(h));
        // combinations of the H-values (main, aux) and of the coefficients (quot)
        let mut vz = vec![EF::ZERO; t_rows];
        let mut vg = vec![EF::ZERO; t_rows];
        let mut cq_poly = vec![EF::ZERO; t_rows];
        let (mut cst_z, mut cst_gz) = (EF::ZERO, EF::ZERO);
        let mut i = 0;
        for &t in &ts {
            let w = sch.w_main[t];
            let wa = sch.w_aux[t];
            let nq = sch.n_quot[t];
            let v = &ood[ood_off[t]..ood_off[t] + sch.ood_len(t)];
            let cz = &coeffs[i..i + w];
            let cgz = &coeffs[i + w..i + 2 * w];
            let caz = &coeffs[i + 2 * w..i + 2 * w + wa];
            let cag = &coeffs[i + 2 * w + wa..i + 2 * w + 2 * wa];
            let cq = &coeffs[i + 2 * w + 2 * wa..i + 2 * w + 2 * wa + nq];
            for col in 0..w {
                cst_z += cz[col] * v[col];
                cst_gz += cgz[col] * v[w + col];
            }
            for col in 0..wa {
                cst_z += caz[col] * v[2 * w + col];
                cst_gz += cag[col] * v[2 * w + wa + col];
            }
            for m in 0..nq {
                cst_z += cq[m] * v[2 * w + 2 * wa + m];
            }
            let ck = chunk;
            for (c0, c1) in main[t].chunks(ck) {
                let vals = main[t].values(&dft, c0, c1);
                combine_into(&mut vz, &vals, &cz[c0..c1]);
                combine_into(&mut vg, &vals, &cgz[c0..c1]);
            }
            let lift = |c: &[EF]| -> Vec<EF> { (0..8 * c.len()).map(|k| c[k / 8] * xpow(k % 8)).collect() };
            if wa > 0 {
                let (lz, lg2) = (lift(caz), lift(cag));
                for (c0, c1) in aux[t].chunks(ck) {
                    let vals = aux[t].values(&dft, c0, c1);
                    combine_into(&mut vz, &vals, &lz[c0..c1]);
                    combine_into(&mut vg, &vals, &lg2[c0..c1]);
                }
            }
            if let Src::Coeffs(qc) = &quot[t] {
                combine_into(&mut cq_poly, qc, &lift(cq));
            }
            i += sch.ood_len(t);
        }
        // coefficients of P_z (= iDFT(vz) + quotient part) and P_gz
        let mut pz = dft.idft_batch(RowMajorMatrix::new(ef_to_base_row(&vz), 8));
        drop(vz);
        for (r, x) in cq_poly.iter().enumerate() {
            for (l, c) in ef_coeffs(x).iter().enumerate() {
                pz.values[8 * r + l] += *c;
            }
        }
        drop(cq_poly);
        let pg = dft.idft_batch(RowMajorMatrix::new(ef_to_base_row(&vg), 8));
        drop(vg);
        let mut both = vec![F::ZERO; t_rows * 16];
        both.par_chunks_mut(16).enumerate().for_each(|(r, o)| {
            o[..8].copy_from_slice(&pz.values[8 * r..8 * r + 8]);
            o[8..].copy_from_slice(&pg.values[8 * r..8 * r + 8]);
        });
        drop((pz, pg));
        let both = RowMajorMatrix::new(both, 16);
        let sh = class_shift(c);
        let mut g = vec![EF::ZERO; n];
        for b in 0..n / t_rows {
            let p0 = b * t_rows;
            let ev = eval_range(&dft, &both, lg, sh, p0, t_rows, None);
            let xs: Vec<F> = (0..t_rows).map(|u| sh * omega(lg).exp_u64(crate::mmcs::rev(p0 + u, lg) as u64)).collect();
            let iz = batch_multiplicative_inverse(&xs.iter().map(|&x| ef_from_base(x) - z).collect::<Vec<_>>());
            let igz = batch_multiplicative_inverse(&xs.iter().map(|&x| ef_from_base(x) - gz).collect::<Vec<_>>());
            g[p0..p0 + t_rows].par_iter_mut().enumerate().for_each(|(u, o)| {
                let row = &ev.values[16 * u..16 * u + 16];
                let a = ef_from_coeffs(&row[..8]) - cst_z;
                let bb = ef_from_coeffs(&row[8..]) - cst_gz;
                *o = a * iz[u] + bb * igz[u];
            });
        }
        deep.push(g);
    }
    tm.lap("deep");

    // ---- FRI ----
    let two_inv = F::TWO.inverse();
    let mut fri: Vec<(Vec<EF>, Tree)> = vec![];
    let mut fri_roots = vec![];
    let mut f = std::mem::take(&mut deep[0]);
    for k in 0..sch.fri_l {
        if k > 0 {
            if let Some(ci) = sch.class_layers.iter().position(|&c| c == k) {
                let gm = tr.chal();
                f.par_iter_mut().zip(deep[ci].par_iter()).for_each(|(x, d)| *x += gm * *d);
                deep[ci] = vec![];
            }
        }
        let committed = sch.committed_at(k);
        if let Some(i) = committed {
            let a = sch.committed[i].1;
            let tree = fri_commit(&f, a);
            tr.absorb(&[tree.root()], &[]);
            fri_roots.push(tree.root());
            fri.push((vec![], tree));
        }
        let beta = tr.chal();
        let lg = l0 - k;
        let half = 1usize << (lg - 1);
        let mut xs: Vec<F> = omega(lg).shifted_powers(class_shift(k) * F::TWO).take(half).collect();
        reverse_slice_index_bits(&mut xs);
        let inv2x = batch_multiplicative_inverse(&xs);
        let nf: Vec<EF> = (0..half)
            .into_par_iter()
            .map(|j| {
                let (e0, e1) = (f[2 * j], f[2 * j + 1]);
                (e0 + e1) * two_inv + beta * (e0 - e1) * inv2x[j]
            })
            .collect();
        let old = std::mem::replace(&mut f, nf);
        if committed.is_some() {
            fri.last_mut().unwrap().0 = old;
        }
    }
    if sch.fri_l > 0 {
        if let Some(ci) = sch.class_layers.iter().position(|&c| c == sch.fri_l) {
            let gm = tr.chal();
            f.par_iter_mut().zip(deep[ci].par_iter()).for_each(|(x, d)| *x += gm * *d);
        }
    }
    drop(deep);
    let y0 = crate::protocol::point(l0, sch.fri_l, 0);
    let p0 = (f[0] + f[1]) * two_inv;
    let p1 = (f[0] - f[1]) * (F::TWO * y0).inverse();
    for (j, v) in f.iter().enumerate() {
        if *v != p0 + p1 * crate::protocol::point(l0, sch.fri_l, j) {
            return Err("final FRI layer is not of degree < 2 (prover bug or unsatisfied AIR)".into());
        }
    }
    let final_poly = [p0, p1];
    tm.lap("fri");
    tr.absorb(&[], &efs_bytes(&final_poly));
    let queries = tr.finish_queries(l0, NUM_CHUNKS, PER_CHUNK);

    // ---- openings ----
    let open_main = lmcommit::open(&dft, &main_m, &main_tree, &queries, chunk);
    let open_aux = lmcommit::open(&dft, &aux_m, &aux_tree, &queries, chunk);
    let open_quot = lmcommit::open(&dft, &quot_m, &quot_tree, &queries, chunk);
    let open_fri = sch
        .committed
        .iter()
        .zip(&fri)
        .map(|(&(c, a), (fv, t))| {
            let q: Vec<usize> = queries.iter().map(|&j| j >> (c + a)).collect();
            fri_open(fv, a, t, &q)
        })
        .collect();
    tm.lap("openings");
    let proof = Proof {
        heights,
        root_main: main_tree.root(),
        root_aux: aux_tree.root(),
        aux_finals,
        root_quot: quot_tree.root(),
        ood,
        fri_roots,
        final_poly,
        open_main,
        open_aux,
        open_quot,
        open_fri,
    };
    Ok((proof, sch, queries))
}

pub fn prove_bytes(
    air: &Air,
    traces: Vec<RowMajorMatrix<F>>,
    pub_tape: &[u8],
    cb: &[u8],
    opts: &ProveOptions,
) -> Result<Vec<u8>, String> {
    let (p, sch, q) = prove(air, traces, pub_tape, cb, opts)?;
    Ok(p.to_bytes(&sch, &q))
}

pub fn prove_cols_bytes(
    air: &Air,
    traces: Vec<TraceCols>,
    pub_tape: &[u8],
    cb: &[u8],
    opts: &ProveOptions,
) -> Result<Vec<u8>, String> {
    let (p, sch, q) = prove_cols(air, traces, pub_tape, cb, opts)?;
    Ok(p.to_bytes(&sch, &q))
}
