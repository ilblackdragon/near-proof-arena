//! Honest prover for `np-udr-stark-v1`.

use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::{batch_multiplicative_inverse, BasedVectorSpace, Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::{log2_strict_usize, reverse_slice_index_bits};
use rayon::prelude::*;

use crate::air::{Air, Tape};
use crate::field::{ef_coeffs, ef_from_base, ef_from_coeffs, omega, shift, EF, F};
use crate::hash::{Digest32, Digest64};
use crate::mmcs::{self, rev, Mat, Opening, Tree};
use crate::protocol::{batch_coeffs, Proof, Schedule, LOG_BLOWUP, NUM_CHUNKS, PER_CHUNK, VERSION};
use crate::transcript::Transcript;
use crate::verifier::{aux_msg, final_bytes, ood_bytes, public_inputs};

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
    let mut leaves: Vec<Option<Vec<Digest64>>> = (0..=l0).map(|_| None).collect();
    for k in 0..=l0 {
        let ts: Vec<&ColPolys> = polys.iter().filter(|p| p.class == k).collect();
        if ts.is_empty() {
            continue;
        }
        let h = ts[0].log_h;
        let t = 1usize << h;
        let mut lv = Vec::with_capacity(t << LOG_BLOWUP);
        for b in 0..1usize << LOG_BLOWUP {
            let blocks: Vec<RowMajorMatrix<F>> = ts.iter().map(|p| p.block(dft, b)).collect();
            let hs: Vec<Digest64> = (0..t)
                .into_par_iter()
                .map_init(Vec::new, |buf, u| {
                    let rows: Vec<&[F]> =
                        blocks.iter().map(|m| &m.values[u * m.width()..(u + 1) * m.width()]).collect();
                    mmcs::hash_rows(&rows, buf)
                })
                .collect();
            lv.extend(hs);
        }
        leaves[k] = Some(lv);
    }
    mmcs::commit_leaves(l0, leaves)
}

/// Open one round at layer-0 query positions.
fn open_polys(dft: &Dft, polys: &[ColPolys], tree: &Tree, queries: &[usize]) -> Opening {
    let sets = mmcs::index_sets(tree.log_h0, queries);
    let rows = polys
        .iter()
        .map(|p| {
            let s = &sets[p.class];
            let w = p.width();
            let mut out = Vec::with_capacity(s.len() * w);
            let mut cur: Option<(usize, RowMajorMatrix<F>)> = None;
            for &j in s {
                let b = j >> p.log_h;
                if cur.as_ref().map(|c| c.0) != Some(b) {
                    cur = Some((b, p.block(dft, b)));
                }
                let m = &cur.as_ref().unwrap().1;
                let u = j & ((1 << p.log_h) - 1);
                out.extend_from_slice(&m.values[u * w..(u + 1) * w]);
            }
            out
        })
        .collect();
    Opening { rows, siblings: mmcs::siblings(tree, queries) }
}

/// Quotient `C_α / Z_H` of one table, as chunk coefficients (`T × 8·nq`).
fn quotient(
    dft: &Dft,
    tape: &Tape,
    main: &ColPolys,
    nq: usize,
    pubs: &[F],
    alpha: EF,
) -> Result<RowMajorMatrix<F>, String> {
    let h = main.log_h;
    let t = 1usize << h;
    let e = crate::protocol::ceil_log2(nq);
    let tf = F::from_u64(t as u64);
    let h_last = omega(h).inverse();
    let apow: Vec<EF> = alpha.powers().take(tape.outputs.len()).collect();
    let w = main.width();
    // next-row permutation inside a block (bit-reversed order)
    let next: Vec<usize> = (0..t).map(|u| rev((rev(u, h) + 1) % t, h)).collect();
    let mut qv: Vec<EF> = Vec::with_capacity(t << e);
    for b in 0..1usize << e {
        let blk = main.block(dft, b);
        let sh = main.block_shift(b);
        let mut xs: Vec<F> = omega(h).shifted_powers(sh).take(t).collect();
        reverse_slice_index_bits(&mut xs);
        let z = sh.exp_power_of_2(h) - F::ONE;
        let zinv = z.inverse();
        let i1 = batch_multiplicative_inverse(&xs.iter().map(|&x| tf * (x - F::ONE)).collect::<Vec<_>>());
        let i2 = batch_multiplicative_inverse(&xs.iter().map(|&x| tf * (x - h_last)).collect::<Vec<_>>());
        let part: Vec<EF> = (0..t)
            .into_par_iter()
            .map_init(Vec::new, |regs, u| {
                let first = z * i1[u];
                let last = h_last * z * i2[u];
                let row = &blk.values[u * w..(u + 1) * w];
                let nu = next[u];
                let nrow = &blk.values[nu * w..(nu + 1) * w];
                tape.eval::<F>(regs, |c, nn| if nn { nrow[c] } else { row[c] }, pubs, [first, last, F::ONE - last]);
                let mut acc = EF::ZERO;
                for (o, a) in tape.outputs.iter().zip(&apow) {
                    acc += *a * regs[*o as usize];
                }
                acc * zinv
            })
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

pub fn prove(
    air: &Air,
    traces: Vec<RowMajorMatrix<F>>,
    pub_digest: &Digest32,
    cb: &[u8],
    opts: &ProveOptions,
) -> Result<Proof, String> {
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
    let mut tr = Transcript::new(pub_digest, &sch.header_bytes(), cb);

    // ---- round 1: main traces ----
    let main: Vec<ColPolys> = traces
        .into_iter()
        .enumerate()
        .map(|(t, m)| ColPolys { log_h: heights[t], class: sch.class[t], coeffs: dft.idft_batch(m) })
        .collect();
    tm.lap("main iDFT");
    let main_tree = commit_polys(&dft, &main, l0);
    tm.lap("main commit");
    tr.absorb(main_tree.root().to_vec());
    let _alpha_fp = tr.chal();
    let _gamma_mul = tr.chal();

    // ---- round 2: aux (grand products; none yet) ----
    let aux: Vec<ColPolys> = (0..nt)
        .map(|t| ColPolys { log_h: heights[t], class: sch.class[t], coeffs: RowMajorMatrix::new(vec![], 0) })
        .collect();
    let aux_tree = commit_polys(&dft, &aux, l0);
    let aux_finals: Vec<EF> = vec![];
    tr.absorb(aux_msg(&aux_tree.root(), &aux_finals));
    let alpha_c = tr.chal();
    tm.lap("aux commit");

    // ---- round 3: quotient ----
    let tapes: Vec<Tape> = air.tables.iter().map(|t| Tape::compile(&t.constraints)).collect();
    let mut quot = vec![];
    for t in 0..nt {
        let qc = quotient(&dft, &tapes[t], &main[t], sch.n_quot[t], &pubs, alpha_c)
            .map_err(|e| format!("table {t}: {e}"))?;
        quot.push(ColPolys { log_h: heights[t], class: sch.class[t], coeffs: qc });
    }
    tm.lap("quotient");
    let quot_tree = commit_polys(&dft, &quot, l0);
    tm.lap("quot commit");
    tr.absorb(quot_tree.root().to_vec());
    let z = tr.chal_ood();

    // ---- round 4: OOD values ----
    let mut ood = vec![];
    for t in 0..nt {
        let gz = z * ef_from_base(omega(heights[t]));
        ood.extend(eval_at(&main[t].coeffs, z));
        ood.extend(eval_at(&main[t].coeffs, gz));
        let qz = eval_at(&quot[t].coeffs, z);
        for m in 0..sch.n_quot[t] {
            ood.push((0..8).fold(EF::ZERO, |acc, l| acc + xpow(l) * qz[8 * m + l]));
        }
    }
    tm.lap("ood");
    crate::verifier::ali_check(air, &sch, &ood, z, alpha_c, &pubs)
        .map_err(|e| format!("{e}: constraints not satisfied by the trace"))?;
    tr.absorb(ood_bytes(&ood));
    let batch: Vec<Vec<EF>> = sch.batch_bits.iter().map(|&b| (0..b).map(|_| tr.chal()).collect()).collect();

    // ---- DEEP batches per class layer (bit-reversed order) ----
    let mut ood_off = vec![];
    let mut o = 0;
    for t in 0..nt {
        ood_off.push(o);
        o += sch.ood_len(t);
    }
    let deep: Vec<Vec<EF>> = sch
        .class_layers
        .iter()
        .enumerate()
        .map(|(ci, &c)| {
            let lg = l0 - c;
            let n = 1usize << lg;
            let ts = sch.tables_of(c);
            let h = heights[ts[0]];
            let coeffs = batch_coeffs(&batch[ci], sch.batch_len[ci]);
            let gz = z * ef_from_base(omega(h));
            let mut pz = vec![EF::ZERO; 1 << h];
            let mut pgz = vec![EF::ZERO; 1 << h];
            let mut cst_z = EF::ZERO;
            let mut cst_gz = EF::ZERO;
            let mut i = 0;
            for &t in &ts {
                let w = sch.w_main[t];
                let nq = sch.n_quot[t];
                let v = &ood[ood_off[t]..ood_off[t] + sch.ood_len(t)];
                let cz = &coeffs[i..i + w];
                let cgz = &coeffs[i + w..i + 2 * w];
                let cq = &coeffs[i + 2 * w..i + 2 * w + nq];
                for col in 0..w {
                    cst_z += cz[col] * v[col];
                    cst_gz += cgz[col] * v[w + col];
                }
                for m in 0..nq {
                    cst_z += cq[m] * v[2 * w + m];
                }
                combine_into(&mut pz, &main[t].coeffs, cz);
                combine_into(&mut pgz, &main[t].coeffs, cgz);
                // quotient chunk m is K-valued: Σ_l X^l·q_{m,l}; coefficient
                // of base column 8m+l is cq[m]·X^l
                let qcoef: Vec<EF> = (0..8 * nq).map(|k| cq[k / 8] * xpow(k % 8)).collect();
                combine_into(&mut pz, &quot[t].coeffs, &qcoef);
                i += sch.ood_len(t);
            }
            // evaluate both on the class LDE
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
    for k in 0..sch.fri_l {
        if let Some(i) = sch.committed_at(k) {
            let a = sch.committed[i].1;
            let mat = Mat { width: 8 << a, log_height: l0 - k - a, values: ef_to_base_row(&f), bitrev: false };
            let tree = mmcs::commit(std::slice::from_ref(&mat));
            tr.absorb(tree.root().to_vec());
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
        if let Some(ci) = sch.class_layers.iter().position(|&c| c == k + 1) {
            let gamma = tr.chal();
            f.par_iter_mut().zip(deep[ci].par_iter()).for_each(|(x, g)| *x += gamma * *g);
        }
    }
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
    tr.absorb(final_bytes(&final_poly));
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
    Ok(Proof {
        heights,
        version: VERSION,
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
    })
}
