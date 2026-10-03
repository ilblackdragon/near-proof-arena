//! Honest prover for `np-udr-stark-v1`.

use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::{batch_multiplicative_inverse, Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::{log2_strict_usize, reverse_slice_index_bits};
use rayon::prelude::*;

use crate::air::{Air, Tape};
use crate::field::{ef_coeffs, ef_from_base, ef_from_coeffs, omega, shift, EF, F};
use crate::hash::Digest32;
use crate::mmcs::{self, Mat, Tree};
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

/// `f(ζ)` for every column of a trace given on `⟨ω_T⟩` (barycentric).
fn ood_eval(trace: &RowMajorMatrix<F>, h: usize, zeta: EF) -> Vec<EF> {
    let t = 1usize << h;
    let w = trace.width();
    let g = omega(h);
    let pts: Vec<F> = g.powers().take(t).collect();
    let den: Vec<EF> = pts.iter().map(|&p| zeta - ef_from_base(p)).collect();
    let inv = batch_multiplicative_inverse(&den);
    let wts: Vec<EF> = inv.iter().zip(&pts).map(|(i, &p)| *i * p).collect();
    let scale = (zeta.exp_power_of_2(h) - EF::ONE) * ef_from_base(F::from_u64(t as u64).inverse());
    let chunk = (t / rayon::current_num_threads().max(1)).max(64);
    let acc = (0..t)
        .into_par_iter()
        .chunks(chunk)
        .map(|rows| {
            let mut acc = vec![EF::ZERO; w];
            for r in rows {
                let row = &trace.values[r * w..(r + 1) * w];
                for c in 0..w {
                    acc[c] += wts[r] * row[c];
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
        );
    acc.into_iter().map(|x| x * scale).collect()
}

struct TableLde {
    /// natural-order LDE, `n_t × w`
    main: RowMajorMatrix<F>,
    /// natural-order quotient-chunk LDE, `n_t × 8·nq`
    quot: RowMajorMatrix<F>,
    /// quotient chunk coefficients, `T × 8·nq`
    quot_coeffs: RowMajorMatrix<F>,
}

/// Quotient `C_α / Z_H` on the LDE, returned as its chunk coefficients.
fn quotient(
    dft: &Dft,
    tape: &Tape,
    lde: &RowMajorMatrix<F>,
    h: usize,
    k: usize,
    nq: usize,
    pubs: &[F],
    alpha: EF,
) -> Result<RowMajorMatrix<F>, String> {
    let t = 1usize << h;
    let lg = h + LOG_BLOWUP;
    let n = 1usize << lg;
    let w = lde.width();
    let s = class_shift(k);
    let xs: Vec<F> = omega(lg).shifted_powers(s).take(n).collect();
    let tf = F::from_u64(t as u64);
    let h_last = omega(h).inverse();
    // Z(x_i) depends only on i mod 16
    let st = s.exp_power_of_2(h);
    let zs: Vec<F> = omega(LOG_BLOWUP).shifted_powers(st).take(1 << LOG_BLOWUP).map(|v| v - F::ONE).collect();
    let zinv = batch_multiplicative_inverse(&zs);
    let d1: Vec<F> = xs.iter().map(|&x| tf * (x - F::ONE)).collect();
    let d2: Vec<F> = xs.iter().map(|&x| tf * (x - h_last)).collect();
    let i1 = batch_multiplicative_inverse(&d1);
    let i2 = batch_multiplicative_inverse(&d2);
    let apow: Vec<EF> = alpha.powers().take(tape.outputs.len()).collect();
    let mask = 1usize << LOG_BLOWUP;
    let q: Vec<EF> = (0..n)
        .into_par_iter()
        .map_init(Vec::new, |regs, i| {
            let z = zs[i % mask];
            let first = z * i1[i];
            let last = h_last * z * i2[i];
            let nx = (i + mask) & (n - 1);
            let row = &lde.values[i * w..(i + 1) * w];
            let nrow = &lde.values[nx * w..(nx + 1) * w];
            tape.eval::<F>(regs, |c, nn| if nn { nrow[c] } else { row[c] }, pubs, [first, last, F::ONE - last]);
            let mut acc = EF::ZERO;
            for (o, a) in tape.outputs.iter().zip(&apow) {
                acc += *a * regs[*o as usize];
            }
            acc * zinv[i % mask]
        })
        .collect();
    let qm = RowMajorMatrix::new(ef_to_base_row(&q), 8);
    let coeffs = dft.coset_idft_batch(qm, s);
    // degree check: coefficients beyond nq·T must vanish (else the trace
    // violates a constraint).
    for j in nq * t..n {
        if coeffs.row_slice(j).unwrap().iter().any(|x| !x.is_zero()) {
            return Err(format!("quotient degree too high (coefficient {j}): constraints not satisfied"));
        }
    }
    // chunk m, coefficient j -> row j, columns 8m..8m+8
    let mut out = RowMajorMatrix::new(vec![F::ZERO; t * 8 * nq], 8 * nq);
    for m in 0..nq {
        for j in 0..t {
            let src = coeffs.row_slice(m * t + j).unwrap();
            out.values[j * 8 * nq + 8 * m..j * 8 * nq + 8 * m + 8].copy_from_slice(&src);
        }
    }
    Ok(out)
}

pub struct ProveOptions {
    pub verbose: bool,
}

pub fn prove(
    air: &Air,
    traces: &[RowMajorMatrix<F>],
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
    let ldes: Vec<RowMajorMatrix<F>> = (0..nt)
        .map(|t| {
            dft.coset_lde_batch(traces[t].clone(), LOG_BLOWUP, class_shift(sch.class[t]))
                .to_row_major_matrix()
        })
        .collect();
    tm.lap("main LDE");
    let main_mats: Vec<Mat> = ldes
        .iter()
        .enumerate()
        .map(|(t, m)| Mat { width: m.width(), log_height: sch.log_lde(t), values: m.values.clone(), bitrev: true })
        .collect();
    let main_tree = mmcs::commit(&main_mats);
    tm.lap("main commit");
    tr.absorb(main_tree.root().to_vec());
    let _alpha_fp = tr.chal();
    let _gamma_mul = tr.chal();

    // ---- round 2: aux (grand products; none yet) ----
    let aux_mats: Vec<Mat> =
        (0..nt).map(|t| Mat { width: 0, log_height: sch.log_lde(t), values: vec![], bitrev: true }).collect();
    let aux_tree = mmcs::commit(&aux_mats);
    let aux_finals: Vec<EF> = vec![];
    tr.absorb(aux_msg(&aux_tree.root(), &aux_finals));
    let alpha_c = tr.chal();
    tm.lap("aux commit");

    // ---- round 3: quotient ----
    let tapes: Vec<Tape> = air.tables.iter().map(|t| Tape::compile(&t.constraints)).collect();
    let mut tabs = vec![];
    for t in 0..nt {
        let qc = quotient(&dft, &tapes[t], &ldes[t], heights[t], sch.class[t], sch.n_quot[t], &pubs, alpha_c)
            .map_err(|e| format!("table {t}: {e}"))?;
        let mut padded = qc.values.clone();
        padded.resize(qc.width() << sch.log_lde(t), F::ZERO);
        let ql = dft
            .coset_dft_batch(RowMajorMatrix::new(padded, qc.width()), class_shift(sch.class[t]))
            .to_row_major_matrix();
        tabs.push(TableLde { main: ldes[t].clone(), quot: ql, quot_coeffs: qc });
    }
    drop(ldes);
    tm.lap("quotient");
    let quot_mats: Vec<Mat> = tabs
        .iter()
        .enumerate()
        .map(|(t, tl)| Mat {
            width: tl.quot.width(),
            log_height: sch.log_lde(t),
            values: tl.quot.values.clone(),
            bitrev: true,
        })
        .collect();
    let quot_tree = mmcs::commit(&quot_mats);
    tm.lap("quot commit");
    tr.absorb(quot_tree.root().to_vec());
    let z = tr.chal_ood();

    // ---- round 4: OOD values ----
    let mut ood = vec![];
    for t in 0..nt {
        let gz = z * ef_from_base(omega(heights[t]));
        ood.extend(ood_eval(&traces[t], heights[t], z));
        ood.extend(ood_eval(&traces[t], heights[t], gz));
        let qc = &tabs[t].quot_coeffs;
        let nq = sch.n_quot[t];
        for m in 0..nq {
            let mut acc = EF::ZERO;
            for j in (0..qc.height()).rev() {
                let r = qc.row_slice(j).unwrap();
                acc = acc * z + ef_from_coeffs(&r[8 * m..8 * m + 8]);
            }
            ood.push(acc);
        }
    }
    tm.lap("ood");
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
            let coeffs = batch_coeffs(&batch[ci], sch.batch_len[ci]);
            let gz = z * ef_from_base(omega(heights[ts[0]]));
            let xs: Vec<F> = omega(lg).shifted_powers(class_shift(c)).take(n).collect();
            let iz = batch_multiplicative_inverse(&xs.iter().map(|&x| ef_from_base(x) - z).collect::<Vec<_>>());
            let igz = batch_multiplicative_inverse(&xs.iter().map(|&x| ef_from_base(x) - gz).collect::<Vec<_>>());
            // per table: coefficient slices and constant offsets
            let mut cst_z = EF::ZERO;
            let mut cst_gz = EF::ZERO;
            let mut parts = vec![]; // (t, cz_main, cgz_main, cz_quot)
            let mut i = 0;
            for &t in &ts {
                let w = sch.w_main[t];
                let nq = sch.n_quot[t];
                let v = &ood[ood_off[t]..ood_off[t] + sch.ood_len(t)];
                let cz: Vec<EF> = coeffs[i..i + w].to_vec();
                let cgz: Vec<EF> = coeffs[i + w..i + 2 * w].to_vec();
                // (aux: none)
                let cq: Vec<EF> = coeffs[i + 2 * w..i + 2 * w + nq].to_vec();
                for col in 0..w {
                    cst_z += cz[col] * v[col];
                    cst_gz += cgz[col] * v[w + col];
                }
                for m in 0..nq {
                    cst_z += cq[m] * v[2 * w + m];
                }
                i += sch.ood_len(t);
                parts.push((t, cz, cgz, cq));
            }
            let mut g: Vec<EF> = (0..n)
                .into_par_iter()
                .map(|r| {
                    let mut a = -cst_z;
                    let mut b = -cst_gz;
                    for (t, cz, cgz, cq) in &parts {
                        let tl = &tabs[*t];
                        let w = tl.main.width();
                        let row = &tl.main.values[r * w..(r + 1) * w];
                        for col in 0..w {
                            a += cz[col] * row[col];
                            b += cgz[col] * row[col];
                        }
                        let qw = tl.quot.width();
                        let qrow = &tl.quot.values[r * qw..(r + 1) * qw];
                        for m in 0..cq.len() {
                            a += cq[m] * ef_from_coeffs(&qrow[8 * m..8 * m + 8]);
                        }
                    }
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
    let open_main = mmcs::open(&main_mats, &main_tree, &queries);
    let open_aux = mmcs::open(&aux_mats, &aux_tree, &queries);
    let open_quot = mmcs::open(&quot_mats, &quot_tree, &queries);
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
