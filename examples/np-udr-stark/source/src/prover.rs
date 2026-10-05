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

/// Rows of selected columns of a source on LDE ranges, written into one half
/// of a two-half buffer (`2·len × width`), so that the next rows of one range
/// can be the current rows of the following range.
struct Halves<'a> {
    src: &'a Src<'a>,
    list: Option<&'a [usize]>,
    width: usize,
    len: usize,
    buf: Vec<F>,
}

impl<'a> Halves<'a> {
    fn new(src: &'a Src<'a>, list: Option<&'a [usize]>, len: usize) -> Self {
        let width = list.map_or(src.width(), |l| l.len());
        Halves { src, list, width, len, buf: vec![F::ZERO; 2 * len * width] }
    }
    /// Evaluate positions `p0 .. p0+len` into half `half`.
    #[allow(clippy::too_many_arguments)]
    fn load(&mut self, dft: &Dft, half: usize, p0: usize, lde: usize, sh: F, chunk: usize) {
        let _t = std::time::Instant::now();
        let (width, len) = (self.width, self.len);
        let parts: Vec<(usize, usize)> = match self.list {
            None => self.src.chunks(chunk),
            Some(l) => (0..l.len().div_ceil(chunk)).map(|i| (i * chunk, ((i + 1) * chunk).min(l.len()))).collect(),
        };
        let dst = &mut self.buf[half * len * width..(half + 1) * len * width];
        for (c0, c1) in parts {
            let co = match self.list {
                None => self.src.coeffs(dft, c0, c1),
                Some(l) => self.src.coeffs_list(dft, &l[c0..c1]),
            };
            let cw = c1 - c0;
            let t = co.height();
            let step = len.min(t);
            for b in 0..len / step {
                let ev = eval_range(dft, &co, lde, sh, p0 + b * step, step, None);
                dst[b * step * width..(b + 1) * step * width].par_chunks_mut(width * 1024).enumerate().for_each(|(k, rows)| {
                    for (i, row) in rows.chunks_mut(width).enumerate() {
                        let r = k * 1024 + i;
                        row[c0..c1].copy_from_slice(&ev.values[r * cw..(r + 1) * cw]);
                    }
                });
            }
        }
        crate::lowmem::prof::add(&crate::lowmem::prof::FILL, _t);
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

/// Quotient of one table as chunk coefficients (`T × 8·nq`). Main
/// constraints and aux (bus) constraints are evaluated in separate pass
/// families over ranges of LDE positions sized by `avail` bytes.
#[allow(clippy::too_many_arguments)]
fn quotient(
    dft: &Dft,
    tape: &Tape,
    main: &Src,
    aux: &Src,
    h: usize,
    class: usize,
    nq: usize,
    q: &QCtx,
    avail: usize,
    chunk: usize,
) -> Result<RowMajorMatrix<F>, String> {
    let t = 1usize << h;
    let e = crate::protocol::ceil_log2(nq);
    let npts = t << e;
    let lde = h + LOG_BLOWUP;
    let sh = class_shift(class);
    let tf = F::from_u64(t as u64);
    let h_last = omega(h).inverse();
    let apow: Vec<EF> = q.alpha_c.powers().take(tape.outputs.len()).collect();
    let a_aux = q.alpha_c.exp_u64(tape.outputs.len() as u64);
    let w = main.width();
    let aw = aux.width();
    let wa = aw / 8;
    let beval = BlockEval::new(tape, q.pubs);
    let mut qv = vec![EF::ZERO; npts];
    const CH: usize = 1024;
    let selectors = |p0: usize, len: usize| -> (Vec<F>, Vec<F>) {
        let xs: Vec<F> = (0..len).map(|i| sh * omega(lde).exp_u64(crate::mmcs::rev(p0 + i, lde) as u64)).collect();
        let zs: Vec<F> = xs.iter().map(|&x| x.exp_power_of_2(h) - F::ONE).collect();
        let i1 = batch_multiplicative_inverse(&xs.iter().map(|&x| tf * (x - F::ONE)).collect::<Vec<_>>());
        let i2 = batch_multiplicative_inverse(&xs.iter().map(|&x| tf * (x - h_last)).collect::<Vec<_>>());
        ((0..len).map(|i| zs[i] * i1[i]).collect(), (0..len).map(|i| h_last * zs[i] * i2[i]).collect())
    };
    // family 1: main-trace constraints (packed evaluator)
    let len = pass_len(2 * w * 4 + 48, avail, npts);
    let mut hm = Halves::new(main, None, len);
    for (load_cur, st) in schedule(npts, t, h, len) {
        if let Some(p) = load_cur {
            hm.load(dft, st.cur, p, lde, sh, chunk);
        }
        if let Some(p) = st.load_next {
            hm.load(dft, 1 - st.cur, p, lde, sh, chunk);
        }
        let (sfirst, slast) = selectors(st.p0, len);
        let next32 = next_index(&st, len, t, h);
        let tb0 = std::time::Instant::now();
        let row0 = st.cur * len;
        qv[st.p0..st.p0 + len].par_chunks_mut(CH).enumerate().for_each(|(ci, o)| {
            let r0 = ci * CH;
            let r1 = r0 + o.len();
            beval.eval_rows(&hm.buf, w, row0 + r0, &next32[r0..r1], &sfirst[r0..r1], &slast[r0..r1], &apow, o);
        });
        crate::lowmem::prof::add(&crate::lowmem::prof::BEVAL, tb0);
    }
    drop(hm);
    // family 2: aux constraints (interaction columns + aux columns)
    if wa > 0 {
        let rc: Vec<usize> = match aux {
            Src::Aux(a) => a.cols.clone(),
            _ => unreachable!(),
        };
        let mut map = vec![u32::MAX; w];
        for (j, &c) in rc.iter().enumerate() {
            map[c] = j as u32;
        }
        let len = pass_len(2 * (rc.len() + aw) * 4 + 48, avail, npts);
        let mut hi = Halves::new(main, Some(&rc), len);
        let mut ha = Halves::new(aux, None, len);
        let iw = rc.len();
        for (load_cur, st) in schedule(npts, t, h, len) {
            if let Some(p) = load_cur {
                hi.load(dft, st.cur, p, lde, sh, chunk);
                ha.load(dft, st.cur, p, lde, sh, chunk);
            }
            if let Some(p) = st.load_next {
                hi.load(dft, 1 - st.cur, p, lde, sh, chunk);
                ha.load(dft, 1 - st.cur, p, lde, sh, chunk);
            }
            let (sfirst, slast) = selectors(st.p0, len);
            let next32 = next_index(&st, len, t, h);
            let ta0 = std::time::Instant::now();
            let (ibuf, abuf) = (&hi.buf, &ha.buf);
            let row0 = st.cur * len;
            qv[st.p0..st.p0 + len].par_iter_mut().enumerate().for_each_init(
                || (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new()),
                |(iregs, cs, phis, ivals, av, anv), (u, acc)| {
                    let sel = [sfirst[u], slast[u], F::ONE - slast[u]];
                    let ru = row0 + u;
                    let nu = next32[u] as usize;
                    let row = &ibuf[ru * iw..(ru + 1) * iw];
                    let nrow = &ibuf[nu * iw..(nu + 1) * iw];
                    let col = |c: usize, nn: bool| {
                        let j = map[c] as usize;
                        if nn { nrow[j] } else { row[j] }
                    };
                    q.lay.itape.eval::<F>(iregs, col, q.pubs, sel);
                    ivals.clear();
                    ivals.extend(q.lay.itape.outputs.iter().map(|&o| ef_from_base(iregs[o as usize])));
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
    // divide by the zerofier
    qv.par_chunks_mut(1 << 16).enumerate().for_each(|(k, o)| {
        let p0 = k << 16;
        let zs: Vec<F> = (0..o.len())
            .map(|i| (sh * omega(lde).exp_u64(crate::mmcs::rev(p0 + i, lde) as u64)).exp_power_of_2(h) - F::ONE)
            .collect();
        let zi = batch_multiplicative_inverse(&zs);
        for (x, z) in o.iter_mut().zip(zi) {
            *x *= z;
        }
    });
    reverse_slice_index_bits(&mut qv);
    let coeffs = dft.coset_idft_batch(RowMajorMatrix::new(ef_to_base_row(&qv), 8), sh);
    drop(qv);
    for j in nq * t..npts {
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

    // ---- message 0: header ‖ main commitment ----
    let main: Vec<Src> = traces.iter().map(Src::Main).collect();
    let main_m = cmats(&sch, &main);
    let main_tree = lmcommit::commit(&dft, &main_m, l0, group, chunk);
    tm.lap("main commit");
    tr.absorb(&[main_tree.root()], &sch.header_bytes());
    let alpha_fp = tr.chal();
    let gamma = tr.chal();

    // ---- message 2: aux (grand products) ‖ finals ----
    let aux: Vec<Src> = (0..nt)
        .map(|t| Src::Aux(AuxSrc::new(&traces[t], &air.tables[t], &lays[t], &pubs, alpha_fp, gamma)))
        .collect();
    let mut aux_finals = vec![];
    for a in &aux {
        if let Src::Aux(a) = a {
            aux_finals.extend(a.finals());
        }
    }
    let aux_m = cmats(&sch, &aux);
    let aux_tree = lmcommit::commit(&dft, &aux_m, l0, group, chunk);
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
        let q = QCtx { tab: &air.tables[t], lay: &lays[t], alpha_fp, gamma, alpha_c, fins, pubs: &pubs };
        let qpts = (1usize << heights[t]) << crate::protocol::ceil_log2(sch.n_quot[t]);
        let avail = bud.avail(resident + qpts * 32 * 2);
        let qc = quotient(&dft, &tapes[t], &main[t], &aux[t], heights[t], sch.class[t], sch.n_quot[t], &q, avail, chunk)
            .map_err(|e| format!("table {t}: {e}"))?;
        quot.push(Src::Coeffs(qc));
    }
    tm.lap("quotient");
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
