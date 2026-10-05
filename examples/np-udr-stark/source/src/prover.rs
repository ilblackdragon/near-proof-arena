//! Honest prover for `np-udr-stark-v1`.

use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::{batch_multiplicative_inverse, BasedVectorSpace, Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::{log2_strict_usize, reverse_slice_index_bits};
use rayon::prelude::*;

use crate::air::{Air, Table, Tape};
use crate::aux::{aux_constraints, AuxLayout};
use crate::field::{ef_coeffs, ef_from_base, ef_from_coeffs, omega, shift, EF, F};
use crate::hash::Digest64;
use crate::mmcs::{self, rev, Mat, Opening, Tree};
use crate::protocol::{batch_coeffs, Proof, Schedule, LOG_BLOWUP, NUM_CHUNKS, PER_CHUNK};
use crate::transcript::Transcript;
use crate::verifier::{efs_bytes, global_checks, ood_offsets, public_inputs, Challenges};

/// Optional timing log.
pub struct Timer {
    t: std::time::Instant,
    pub on: bool,
}
impl Timer {
    pub fn new(on: bool) -> Self {
        Timer { t: std::time::Instant::now(), on }
    }
    pub fn lap(&mut self, what: &str) {
        if self.on {
            eprintln!("[prove] {what}: {:.3}s", self.t.elapsed().as_secs_f64());
        }
        self.t = std::time::Instant::now();
    }
}

type Dft = Radix2DitParallel<F>;

/// `s^{2^k}` — the coset shift of class `k`.
fn class_shift(k: usize) -> F {
    shift().exp_power_of_2(k)
}

fn ef_to_base_row(v: &[EF]) -> Vec<F> {
    let mut out = Vec::with_capacity(v.len() * 8);
    for x in v {
        out.extend_from_slice(ef_coeffs(x));
    }
    out
}

/// The column polynomials of one table in one round, in coefficient form
/// (`T × w`, row `i` = coefficient of `x^i`). The LDE (size `16·T`, stored
/// bit-reversed) is never materialized: bit-reversed positions
/// `[b·T, (b+1)·T)` form *block* `b`, the coset
/// `s^{2^k}·ω_l^{bitrev_4(b)}·⟨ω_T⟩` in bit-reversed order, recomputed on
/// demand with one size-`T` DFT.
pub struct ColPolys {
    pub log_h: usize,
    pub class: usize,
    pub coeffs: RowMajorMatrix<F>,
}

impl ColPolys {
    fn width(&self) -> usize {
        self.coeffs.width()
    }
    fn log_lde(&self) -> usize {
        self.log_h + LOG_BLOWUP
    }
    fn block_shift(&self, b: usize) -> F {
        class_shift(self.class) * omega(self.log_lde()).exp_u64(rev(b, LOG_BLOWUP) as u64)
    }
    /// Evaluations on block `b` (`T × w`, bit-reversed order within).
    fn block(&self, dft: &Dft, b: usize) -> RowMajorMatrix<F> {
        let t = 1usize << self.log_h;
        if self.width() == 0 {
            return RowMajorMatrix::new(vec![], 0);
        }
        let mut m = dft.coset_dft_batch(self.coeffs.clone(), self.block_shift(b)).to_row_major_matrix();
        debug_assert_eq!(m.height(), t);
        reverse_matrix_index_bits(&mut m);
        m
    }
}

/// Evaluation of every column at `zeta`.
fn eval_at(c: &RowMajorMatrix<F>, zeta: EF) -> Vec<EF> {
    let t = c.height();
    let w = c.width();
    let zp: Vec<EF> = zeta.powers().take(t).collect();
    let chunk = (t / rayon::current_num_threads().max(1)).max(64);
    (0..t)
        .into_par_iter()
        .chunks(chunk)
        .map(|rows| {
            let mut acc = vec![EF::ZERO; w];
            for r in rows {
                let row = &c.values[r * w..(r + 1) * w];
                for k in 0..w {
                    acc[k] += zp[r] * row[k];
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

/// `out[r] += Σ_k coef[k]·c[r][k]` (EF polynomial combination).
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

/// Commit one round (one matrix per table) without materializing the LDE.
fn commit_polys(dft: &Dft, polys: &[ColPolys], l0: usize) -> Tree {
    let mut levels: Vec<Vec<Digest64>> = vec![];
    for k in 0..=l0 {
        let ts: Vec<&ColPolys> = polys.iter().filter(|p| p.class == k).collect();
        if ts.is_empty() {
            assert!(k > 0, "no level-0 matrix");
            let lv = mmcs::plain_level(k, &levels[k - 1]);
            levels.push(lv);
            continue;
        }
        let h = ts[0].log_h;
        let t = 1usize << h;
        let mut lv = Vec::with_capacity(t << LOG_BLOWUP);
        for b in 0..1usize << LOG_BLOWUP {
            let blocks: Vec<RowMajorMatrix<F>> = ts.iter().map(|p| p.block(dft, b)).collect();
            let prev = levels.last();
            let hs: Vec<Digest64> = (0..t)
                .into_par_iter()
                .map_init(Vec::new, |buf, u| {
                    let rows: Vec<&[F]> =
                        blocks.iter().map(|m| &m.values[u * m.width()..(u + 1) * m.width()]).collect();
                    if k == 0 {
                        mmcs::hash_rows(&rows, buf)
                    } else {
                        let j = b * t + u;
                        let p = prev.unwrap();
                        mmcs::hash_node_rows(k, &p[2 * j], &p[2 * j + 1], &rows, buf)
                    }
                })
                .collect();
            lv.extend(hs);
        }
        levels.push(lv);
    }
    Tree { log_h0: l0, levels }
}

/// Rows of a coefficient matrix evaluated at base-field points:
/// `out[p] = Σ_i x_p^i · coeffs[i]` (one pass over the coefficients, packed
/// over columns, parallel over column chunks).
pub fn eval_rows_at(coeffs: &RowMajorMatrix<F>, xs: &[F]) -> Vec<Vec<F>> {
    use p3_field::PackedValue;
    type P = <F as Field>::Packing;
    let w = coeffs.width();
    let t = coeffs.height();
    let np = xs.len();
    if w == 0 || np == 0 {
        return vec![vec![]; np];
    }
    let lanes = P::WIDTH;
    let chunk = (64 * lanes).min(w.next_multiple_of(lanes));
    let nchunks = w.div_ceil(chunk);
    let parts: Vec<Vec<Vec<F>>> = (0..nchunks)
        .into_par_iter()
        .map(|c| {
            let c0 = c * chunk;
            let cw = chunk.min(w - c0);
            let full = cw / lanes;
            let mut acc = vec![P::ZERO; np * full];
            let mut tail = vec![F::ZERO; np * (cw - full * lanes)];
            let mut pw: Vec<F> = vec![F::ONE; np];
            for i in 0..t {
                let row = &coeffs.values[i * w + c0..i * w + c0 + cw];
                let packed = P::pack_slice(&row[..full * lanes]);
                for p in 0..np {
                    let x = P::from(pw[p]);
                    let a = &mut acc[p * full..(p + 1) * full];
                    for (av, rv) in a.iter_mut().zip(packed) {
                        *av += x * *rv;
                    }
                    let tl = cw - full * lanes;
                    for k in 0..tl {
                        tail[p * tl + k] += pw[p] * row[full * lanes + k];
                    }
                    pw[p] *= xs[p];
                }
            }
            (0..np)
                .map(|p| {
                    let mut v = P::unpack_slice(&acc[p * full..(p + 1) * full]).to_vec();
                    let tl = cw - full * lanes;
                    v.extend_from_slice(&tail[p * tl..(p + 1) * tl]);
                    v
                })
                .collect()
        })
        .collect();
    (0..np)
        .map(|p| {
            let mut v = Vec::with_capacity(w);
            for part in &parts {
                v.extend_from_slice(&part[p]);
            }
            v
        })
        .collect()
}

/// Open one round at layer-0 query positions.
fn open_polys(_dft: &Dft, polys: &[ColPolys], tree: &Tree, queries: &[usize]) -> Opening {
    let l0 = tree.log_h0;
    let sets = mmcs::index_sets(l0, queries);
    let rows = polys
        .iter()
        .map(|p| {
            let s = &sets[p.class];
            let xs: Vec<F> = s.iter().map(|&j| crate::protocol::point(l0, p.class, j)).collect();
            eval_rows_at(&p.coeffs, &xs).concat()
        })
        .collect();
    Opening { rows, siblings: mmcs::siblings(tree, queries) }
}

/// Challenges and bus finals the quotient of one table depends on.
pub struct QuotCtx<'a> {
    pub tab: &'a Table,
    pub lay: &'a AuxLayout,
    pub alpha_fp: EF,
    pub gamma: EF,
    pub alpha_c: EF,
    pub fins: &'a [EF],
}

/// Grand-product aux trace of one table on the trace domain (`T × 8·wa`
/// base limbs, natural row order) and its bus finals (FORMATS.md §3).
fn aux_trace(
    main: &RowMajorMatrix<F>,
    h: usize,
    tab: &Table,
    lay: &AuxLayout,
    pubs: &[F],
    alpha: EF,
    gamma: EF,
) -> (RowMajorMatrix<F>, Vec<EF>) {
    let t = 1usize << h;
    let w = main.width();
    let wa = lay.width();
    if wa == 0 {
        return (RowMajorMatrix::new(vec![], 0), vec![]);
    }
    // per row: chain columns and group factors Φ
    let rows: Vec<(Vec<EF>, Vec<EF>)> = (0..t)
        .into_par_iter()
        .map_init(Vec::new, |regs, r| {
            let row = &main.values[r * w..(r + 1) * w];
            let nr = (r + 1) % t;
            let nrow = &main.values[nr * w..(nr + 1) * w];
            let sel = [
                if r == 0 { F::ONE } else { F::ZERO },
                if r + 1 == t { F::ONE } else { F::ZERO },
                if r + 1 == t { F::ZERO } else { F::ONE },
            ];
            lay.itape.eval::<F>(regs, |c, n| if n { nrow[c] } else { row[c] }, pubs, sel);
            let ivals: Vec<EF> = lay.itape.outputs.iter().map(|&o| ef_from_base(regs[o as usize])).collect();
            let mut chain = vec![EF::ZERO; lay.n_chain];
            let mut phis = Vec::with_capacity(tab.interactions.len());
            for (ii, it) in tab.interactions.iter().enumerate() {
                let o = lay.expr_off[ii];
                let msg = &ivals[o..o + it.msg.len()];
                let bits = &ivals[o + it.msg.len()..o + it.msg.len() + it.mult.len()];
                let p0 = gamma - crate::aux::fingerprint(it.bus, msg, alpha);
                let k = bits.len();
                match k {
                    0 => phis.push(EF::ONE),
                    1 => phis.push(EF::ONE + bits[0] * (p0 - EF::ONE)),
                    _ => {
                        let off = lay.chain[ii].1;
                        let mut p = p0;
                        let mut pi = EF::ONE + bits[0] * (p0 - EF::ONE);
                        for j in 0..k - 1 {
                            p = p * p;
                            chain[off + j] = p;
                            pi *= EF::ONE + bits[j + 1] * (p - EF::ONE);
                            chain[off + k - 1 + j] = pi;
                        }
                        phis.push(pi);
                    }
                }
            }
            let gphi: Vec<EF> = lay.groups.iter().map(|g| g.iter().fold(EF::ONE, |a, &i| a * phis[i])).collect();
            (chain, gphi)
        })
        .collect();
    let ng = lay.groups.len();
    let mut out = vec![F::ZERO; t * 8 * wa];
    let mut acc = vec![EF::ONE; ng];
    for r in 0..t {
        let (chain, gphi) = &rows[r];
        let dst = &mut out[r * 8 * wa..(r + 1) * 8 * wa];
        for (c, v) in chain.iter().chain(acc.iter()).enumerate() {
            dst[8 * c..8 * c + 8].copy_from_slice(ef_coeffs(v));
        }
        for g in 0..ng {
            acc[g] *= gphi[g];
        }
    }
    (RowMajorMatrix::new(out, 8 * wa), acc)
}

/// Quotient `C_α / Z_H` of one table, as chunk coefficients (`T × 8·nq`).
fn quotient(
    dft: &Dft,
    tape: &Tape,
    main: &ColPolys,
    aux: &ColPolys,
    nq: usize,
    pubs: &[F],
    q: &QuotCtx,
) -> Result<RowMajorMatrix<F>, String> {
    let h = main.log_h;
    let t = 1usize << h;
    let e = crate::protocol::ceil_log2(nq);
    let tf = F::from_u64(t as u64);
    let h_last = omega(h).inverse();
    let apow: Vec<EF> = q.alpha_c.powers().take(tape.outputs.len()).collect();
    let a_aux = q.alpha_c.exp_u64(tape.outputs.len() as u64);
    let w = main.width();
    let wa = q.lay.width();
    // next-row permutation inside a block (bit-reversed order)
    let next: Vec<usize> = (0..t).map(|u| rev((rev(u, h) + 1) % t, h)).collect();
    let mut qv: Vec<EF> = Vec::with_capacity(t << e);
    for b in 0..1usize << e {
        let blk = main.block(dft, b);
        let ablk = aux.block(dft, b);
        let sh = main.block_shift(b);
        let mut xs: Vec<F> = omega(h).shifted_powers(sh).take(t).collect();
        reverse_slice_index_bits(&mut xs);
        let z = sh.exp_power_of_2(h) - F::ONE;
        let zinv = z.inverse();
        let i1 = batch_multiplicative_inverse(&xs.iter().map(|&x| tf * (x - F::ONE)).collect::<Vec<_>>());
        let i2 = batch_multiplicative_inverse(&xs.iter().map(|&x| tf * (x - h_last)).collect::<Vec<_>>());
        let part: Vec<EF> = (0..t)
            .into_par_iter()
            .map_init(
                || (Vec::new(), Vec::new(), Vec::new(), Vec::new()),
                |(regs, iregs, cs, phis), u| {
                    let first = z * i1[u];
                    let last = h_last * z * i2[u];
                    let sel = [first, last, F::ONE - last];
                    let row = &blk.values[u * w..(u + 1) * w];
                    let nu = next[u];
                    let nrow = &blk.values[nu * w..(nu + 1) * w];
                    let col = |c: usize, nn: bool| if nn { nrow[c] } else { row[c] };
                    tape.eval::<F>(regs, col, pubs, sel);
                    let mut acc = EF::ZERO;
                    for (o, a) in tape.outputs.iter().zip(&apow) {
                        acc += *a * regs[*o as usize];
                    }
                    if wa > 0 {
                        q.lay.itape.eval::<F>(iregs, col, pubs, sel);
                        let ivals: Vec<EF> =
                            q.lay.itape.outputs.iter().map(|&o| ef_from_base(iregs[o as usize])).collect();
                        let ar = &ablk.values[u * 8 * wa..(u + 1) * 8 * wa];
                        let an = &ablk.values[nu * 8 * wa..(nu + 1) * 8 * wa];
                        let av: Vec<EF> = (0..wa).map(|c| ef_from_coeffs(&ar[8 * c..8 * c + 8])).collect();
                        let anv: Vec<EF> = (0..wa).map(|c| ef_from_coeffs(&an[8 * c..8 * c + 8])).collect();
                        cs.clear();
                        let sele = sel.map(ef_from_base);
                        aux_constraints(q.tab, q.lay, &ivals, q.alpha_fp, q.gamma, &av, &anv, q.fins, sele, cs, phis);
                        let mut pw = a_aux;
                        for c in cs.iter() {
                            acc += pw * *c;
                            pw *= q.alpha_c;
                        }
                    }
                    acc * zinv
                },
            )
            .collect();
        qv.extend(part);
    }
    // first 2^e blocks = coset s^{2^k}·⟨ω_{h+e}⟩, bit-reversed
    reverse_slice_index_bits(&mut qv);
    let coeffs = dft.coset_idft_batch(RowMajorMatrix::new(ef_to_base_row(&qv), 8), class_shift(main.class));
    for j in nq * t..(t << e) {
        if coeffs.row_slice(j).unwrap().iter().any(|x| !x.is_zero()) {
            return Err(format!("quotient degree too high (coefficient {j}): constraints not satisfied"));
        }
    }
    let mut out = RowMajorMatrix::new(vec![F::ZERO; t * 8 * nq], 8 * nq);
    for m in 0..nq {
        for j in 0..t {
            let src = coeffs.row_slice(m * t + j).unwrap();
            out.values[j * 8 * nq + 8 * m..j * 8 * nq + 8 * m + 8].copy_from_slice(&src);
        }
    }
    Ok(out)
}

/// `X^l` in `K`.
fn xpow(l: usize) -> EF {
    EF::from_basis_coefficients_fn(|j| if j == l { F::ONE } else { F::ZERO })
}

fn reverse_matrix_index_bits(m: &mut RowMajorMatrix<F>) {
    let w = m.width();
    let h = m.height();
    if w == 0 || h <= 2 {
        return; // bitrev on <= 1 bit is the identity
    }
    let bits = log2_strict_usize(h);
    for i in 0..h {
        let j = rev(i, bits);
        if i < j {
            let (a, b) = m.values.split_at_mut(j * w);
            a[i * w..(i + 1) * w].swap_with_slice(&mut b[..w]);
        }
    }
}

pub struct ProveOptions {
    pub verbose: bool,
}

/// Prove; returns the proof, its schedule and the query positions (needed by
/// the serializer, FORMATS.md §5).
pub fn prove(
    air: &Air,
    traces: Vec<RowMajorMatrix<F>>,
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
        if tr.width() != air.tables[t].width || !tr.height().is_power_of_two() {
            return Err(format!("table {t}: bad trace shape"));
        }
    }
    let heights: Vec<usize> = traces.iter().map(|m| log2_strict_usize(m.height())).collect();
    let sch = Schedule::new(air, &heights)?;
    let nt = sch.num_tables();
    let l0 = sch.l0;
    let pubs = public_inputs(air, cb);
    let dft = Dft::default();
    let mut tr = Transcript::new(pub_tape, cb);
    let lays: Vec<AuxLayout> = air.tables.iter().map(AuxLayout::new).collect();

    // ---- message 0: header ‖ main commitment ----
    let main: Vec<ColPolys> = traces
        .iter()
        .enumerate()
        .map(|(t, m)| ColPolys { log_h: heights[t], class: sch.class[t], coeffs: dft.idft_batch(m.clone()) })
        .collect();
    tm.lap("main iDFT");
    let main_tree = commit_polys(&dft, &main, l0);
    tm.lap("main commit");
    tr.absorb(&[main_tree.root()], &sch.header_bytes());
    let alpha_fp = tr.chal();
    let gamma = tr.chal();

    // ---- message 2: aux (grand products) ‖ finals ----
    let mut aux = vec![];
    let mut aux_finals = vec![];
    for t in 0..nt {
        let (at, fins) = aux_trace(&traces[t], heights[t], &air.tables[t], &lays[t], &pubs, alpha_fp, gamma);
        aux_finals.extend(fins);
        let coeffs = if at.width() == 0 { at } else { dft.idft_batch(at) };
        aux.push(ColPolys { log_h: heights[t], class: sch.class[t], coeffs });
    }
    drop(traces);
    let aux_tree = commit_polys(&dft, &aux, l0);
    tr.absorb(&[aux_tree.root()], &efs_bytes(&aux_finals));
    let alpha_c = tr.chal();
    tm.lap("aux");

    // ---- message 3: quotient ----
    let tapes: Vec<Tape> = air.tables.iter().map(|t| Tape::compile(&t.constraints)).collect();
    let mut quot = vec![];
    let mut foff = 0;
    for t in 0..nt {
        let fins = &aux_finals[foff..foff + sch.n_finals[t]];
        foff += sch.n_finals[t];
        let qctx = QuotCtx { tab: &air.tables[t], lay: &lays[t], alpha_fp, gamma, alpha_c, fins };
        let qc = quotient(&dft, &tapes[t], &main[t], &aux[t], sch.n_quot[t], &pubs, &qctx)
            .map_err(|e| format!("table {t}: {e}"))?;
        quot.push(ColPolys { log_h: heights[t], class: sch.class[t], coeffs: qc });
    }
    tm.lap("quotient");
    let quot_tree = commit_polys(&dft, &quot, l0);
    tm.lap("quot commit");
    tr.absorb(&[quot_tree.root()], &[]);
    let z = tr.chal_ood();

    // ---- message 4: OOD values ----
    let kvals = |v: Vec<EF>, n: usize| -> Vec<EF> {
        (0..n).map(|m| (0..8).fold(EF::ZERO, |acc, l| acc + xpow(l) * v[8 * m + l])).collect()
    };
    let mut ood = vec![];
    for t in 0..nt {
        let gz = z * ef_from_base(omega(heights[t]));
        ood.extend(eval_at(&main[t].coeffs, z));
        ood.extend(eval_at(&main[t].coeffs, gz));
        let wa = sch.w_aux[t];
        if wa > 0 {
            ood.extend(kvals(eval_at(&aux[t].coeffs, z), wa));
            ood.extend(kvals(eval_at(&aux[t].coeffs, gz), wa));
        }
        ood.extend(kvals(eval_at(&quot[t].coeffs, z), sch.n_quot[t]));
    }
    tm.lap("ood");
    let pre = Challenges {
        alpha_fp,
        gamma_mul: gamma,
        alpha_c,
        z,
        batch: vec![],
        beta: vec![],
        gamma_roll: vec![],
        queries: vec![],
    };
    global_checks(air, &sch, &ood, &aux_finals, &pre, &pubs)
        .map_err(|e| format!("{e}: the trace does not satisfy the AIR"))?;
    tr.absorb(&[], &efs_bytes(&ood));
    let batch: Vec<EF> = (0..sch.batch_rounds).map(|_| tr.chal()).collect();

    // ---- DEEP batches per class layer (bit-reversed order) ----
    let ood_off = ood_offsets(&sch);
    let deep: Vec<Vec<EF>> = sch
        .class_layers
        .iter()
        .enumerate()
        .map(|(ci, &c)| {
            let lg = l0 - c;
            let n = 1usize << lg;
            let ts = sch.tables_of(c);
            let h = heights[ts[0]];
            let coeffs = batch_coeffs(&batch, sch.batch_len[ci]);
            let gz = z * ef_from_base(omega(h));
            let mut pz = vec![EF::ZERO; 1 << h];
            let mut pgz = vec![EF::ZERO; 1 << h];
            let mut cst_z = EF::ZERO;
            let mut cst_gz = EF::ZERO;
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
                combine_into(&mut pz, &main[t].coeffs, cz);
                combine_into(&mut pgz, &main[t].coeffs, cgz);
                // K-valued columns: base column 8m+l has coefficient c[m]·X^l
                let lift = |c: &[EF]| -> Vec<EF> { (0..8 * c.len()).map(|k| c[k / 8] * xpow(k % 8)).collect() };
                if wa > 0 {
                    combine_into(&mut pz, &aux[t].coeffs, &lift(caz));
                    combine_into(&mut pgz, &aux[t].coeffs, &lift(cag));
                }
                combine_into(&mut pz, &quot[t].coeffs, &lift(cq));
                i += sch.ood_len(t);
            }
            let mut m = ef_to_base_row(&pz.iter().zip(&pgz).flat_map(|(a, b)| [*a, *b]).collect::<Vec<_>>());
            m.resize(16 * n, F::ZERO);
            let ev = dft.coset_dft_batch(RowMajorMatrix::new(m, 16), class_shift(c)).to_row_major_matrix();
            let xs: Vec<F> = omega(lg).shifted_powers(class_shift(c)).take(n).collect();
            let iz = batch_multiplicative_inverse(&xs.iter().map(|&x| ef_from_base(x) - z).collect::<Vec<_>>());
            let igz = batch_multiplicative_inverse(&xs.iter().map(|&x| ef_from_base(x) - gz).collect::<Vec<_>>());
            let mut g: Vec<EF> = (0..n)
                .into_par_iter()
                .map(|r| {
                    let row = &ev.values[16 * r..16 * r + 16];
                    let a = ef_from_coeffs(&row[..8]) - cst_z;
                    let b = ef_from_coeffs(&row[8..]) - cst_gz;
                    a * iz[r] + b * igz[r]
                })
                .collect();
            reverse_slice_index_bits(&mut g);
            g
        })
        .collect();
    tm.lap("deep");

    // ---- FRI ----
    let mut f = deep[0].clone();
    let mut fri_trees: Vec<(Mat, Tree)> = vec![];
    let mut fri_roots = vec![];
    let two_inv = F::TWO.inverse();
    let roll_in = |k: usize, f: &mut Vec<EF>, tr: &mut Transcript| {
        if k > 0 {
            if let Some(ci) = sch.class_layers.iter().position(|&c| c == k) {
                let g = tr.chal();
                f.par_iter_mut().zip(deep[ci].par_iter()).for_each(|(x, d)| *x += g * *d);
            }
        }
    };
    for k in 0..sch.fri_l {
        roll_in(k, &mut f, &mut tr);
        if let Some(i) = sch.committed_at(k) {
            let a = sch.committed[i].1;
            let mat = Mat { width: 8 << a, log_height: l0 - k - a, values: ef_to_base_row(&f), bitrev: false };
            let tree = mmcs::commit(std::slice::from_ref(&mat));
            tr.absorb(&[tree.root()], &[]);
            fri_roots.push(tree.root());
            fri_trees.push((mat, tree));
        }
        let beta = tr.chal();
        let lg = l0 - k;
        let half = 1usize << (lg - 1);
        // 1/(2x) at positions 2j: x = s^{2^k}·ω_{lg}^{bitrev_{lg-1}(j)}
        let mut xs: Vec<F> = omega(lg).shifted_powers(class_shift(k) * F::TWO).take(half).collect();
        reverse_slice_index_bits(&mut xs);
        let inv2x = batch_multiplicative_inverse(&xs);
        f = (0..half)
            .into_par_iter()
            .map(|j| {
                let (e0, e1) = (f[2 * j], f[2 * j + 1]);
                (e0 + e1) * two_inv + beta * (e0 - e1) * inv2x[j]
            })
            .collect();
    }
    roll_in(sch.fri_l, &mut f, &mut tr);
    // final layer: degree < 2 on 32 points
    let y0 = crate::protocol::point(l0, sch.fri_l, 0);
    let p0 = (f[0] + f[1]) * two_inv;
    let p1 = (f[0] - f[1]) * (F::TWO * y0).inverse();
    for (j, v) in f.iter().enumerate() {
        let y = crate::protocol::point(l0, sch.fri_l, j);
        if *v != p0 + p1 * y {
            return Err("final FRI layer is not of degree < 2 (prover bug or unsatisfied AIR)".into());
        }
    }
    let final_poly = [p0, p1];
    tm.lap("fri");
    tr.absorb(&[], &efs_bytes(&final_poly));
    let queries = tr.finish_queries(l0, NUM_CHUNKS, PER_CHUNK);

    // ---- openings ----
    let open_main = open_polys(&dft, &main, &main_tree, &queries);
    let open_aux = open_polys(&dft, &aux, &aux_tree, &queries);
    let open_quot = open_polys(&dft, &quot, &quot_tree, &queries);
    let open_fri = sch
        .committed
        .iter()
        .zip(&fri_trees)
        .map(|(&(c, a), (m, t))| {
            let q: Vec<usize> = queries.iter().map(|&j| j >> (c + a)).collect();
            mmcs::open(std::slice::from_ref(m), t, &q)
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

/// Prove and serialize (FORMATS.md §5).
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
