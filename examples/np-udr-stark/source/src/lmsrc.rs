//! Column sources of the low-memory prover: every committed matrix is
//! available as column chunks, either as values on the trace domain `H`
//! (natural row order, row `r` ↔ `ω_T^r`) or as coefficients, without the
//! whole matrix (or its LDE) ever being resident.
//!
//! * main trace: compact [`TraceCols`];
//! * aux (grand products): recomputed from the main trace and the challenges
//!   on demand ([`AuxSrc`]);
//! * quotient chunks: stored coefficients (`T × 8·nq`, small).

use p3_dft::TwoAdicSubgroupDft;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use rayon::prelude::*;

use crate::air::{Op, Table};
use crate::aux::{fingerprint, AuxLayout};
use crate::cols::TraceCols;
use crate::field::{ef_coeffs, ef_from_base, EF, F};
use crate::lowmem::Dft;

pub enum Src<'a> {
    Main(&'a TraceCols),
    Aux(AuxSrc<'a>),
    /// coefficients `T × w`
    Coeffs(RowMajorMatrix<F>),
    /// coefficients as contiguous column chunks `(c0, T × cw)`, total width
    Chunks(Vec<(usize, RowMajorMatrix<F>)>, usize),
}

impl Src<'_> {
    pub fn log_h(&self) -> usize {
        match self {
            Src::Main(t) => t.log_h,
            Src::Aux(a) => a.main.log_h,
            Src::Coeffs(c) => p3_util::log2_strict_usize(c.height()),
            Src::Chunks(v, _) => p3_util::log2_strict_usize(v[0].1.height()),
        }
    }
    pub fn width(&self) -> usize {
        match self {
            Src::Main(t) => t.width(),
            Src::Aux(a) => 8 * a.lay.width(),
            Src::Coeffs(c) => c.width(),
            Src::Chunks(_, w) => *w,
        }
    }
    /// Values on `H` of base columns `c0..c1`.
    pub fn values(&self, dft: &Dft, c0: usize, c1: usize) -> RowMajorMatrix<F> {
        match self {
            Src::Main(t) => t.chunk(c0, c1),
            Src::Aux(a) => a.values(c0, c1),
            Src::Coeffs(c) => dft.dft_batch(sub_cols(c, c0, c1)).to_row_major_matrix(),
            Src::Chunks(..) => dft.dft_batch(self.coeffs_(dft, c0, c1)).to_row_major_matrix(),
        }
    }
    /// Coefficients of base columns `c0..c1`.
    pub fn coeffs(&self, dft: &Dft, c0: usize, c1: usize) -> RowMajorMatrix<F> {
        let _t = std::time::Instant::now();
        let r = self.coeffs_(dft, c0, c1);
        crate::lowmem::prof::add(&crate::lowmem::prof::COEFFS, _t);
        r
    }
    fn coeffs_(&self, dft: &Dft, c0: usize, c1: usize) -> RowMajorMatrix<F> {
        match self {
            Src::Coeffs(c) => sub_cols(c, c0, c1),
            Src::Chunks(v, _) => {
                if let Some((_, m)) = v.iter().find(|(s, m)| *s == c0 && s + m.width() == c1) {
                    return m.clone();
                }
                // general column range: gather from the covering chunks
                let h = v[0].1.height();
                let cw = c1 - c0;
                let mut out = vec![F::ZERO; h * cw];
                for (s, m) in v {
                    let (a, b) = ((*s).max(c0), (s + m.width()).min(c1));
                    if a >= b {
                        continue;
                    }
                    let mw = m.width();
                    out.par_chunks_mut(cw).enumerate().for_each(|(r, o)| {
                        o[a - c0..b - c0].copy_from_slice(&m.values[r * mw + a - s..r * mw + b - s]);
                    });
                }
                RowMajorMatrix::new(out, cw)
            }
            _ => {
                let v = self.values(dft, c0, c1);
                if v.width() == 0 { v } else { dft.idft_batch(v) }
            }
        }
    }
    /// Coefficients of the base columns `cols` (main traces only: any subset).
    pub fn coeffs_list(&self, dft: &Dft, cols: &[usize]) -> RowMajorMatrix<F> {
        match self {
            Src::Main(t) => {
                let w = cols.len();
                let h = t.height();
                let mut v = vec![F::ZERO; h * w];
                v.par_chunks_mut(w.max(1) * 1024).enumerate().for_each(|(k, rows)| {
                    for (i, row) in rows.chunks_mut(w.max(1)).enumerate() {
                        let r = k * 1024 + i;
                        for (j, &c) in cols.iter().enumerate() {
                            row[j] = t.get(r, c);
                        }
                    }
                });
                let m = RowMajorMatrix::new(v, w);
                if w == 0 { m } else { dft.idft_batch(m) }
            }
            _ => panic!("coeffs_list: main traces only"),
        }
    }

    /// Column chunk boundaries (aux chunks are aligned to K columns).
    pub fn chunks(&self, max: usize) -> Vec<(usize, usize)> {
        let w = self.width();
        let step = (max / 8).max(1) * 8;
        (0..w.div_ceil(step)).map(|i| (i * step, ((i + 1) * step).min(w))).collect()
    }
}

pub fn sub_cols(m: &RowMajorMatrix<F>, c0: usize, c1: usize) -> RowMajorMatrix<F> {
    let w = m.width();
    if c0 == 0 && c1 == w {
        return m.clone();
    }
    let cw = c1 - c0;
    let h = m.height();
    let mut v = vec![F::ZERO; h * cw];
    v.par_chunks_mut(cw.max(1) * 1024).enumerate().for_each(|(k, o)| {
        for (i, row) in o.chunks_mut(cw.max(1)).enumerate() {
            let r = k * 1024 + i;
            row.copy_from_slice(&m.values[r * w + c0..r * w + c1]);
        }
    });
    RowMajorMatrix::new(v, cw)
}

/// Aux columns of one table, recomputed from the main trace.
pub struct AuxSrc<'a> {
    pub main: &'a TraceCols,
    pub tab: &'a Table,
    pub lay: &'a AuxLayout,
    pub pubs: &'a [F],
    pub alpha: EF,
    pub gamma: EF,
    /// main columns the interaction expressions read (sorted)
    pub cols: Vec<usize>,
    /// per interaction: `α^0..α^len` and `(bus+1)·α^len` (fingerprints
    /// computed with base-field message values)
    apow: Vec<(Vec<EF>, EF)>,
}

const RCH: usize = 4096;

impl<'a> AuxSrc<'a> {
    pub fn new(main: &'a TraceCols, tab: &'a Table, lay: &'a AuxLayout, pubs: &'a [F], alpha: EF, gamma: EF) -> Self {
        let mut cols: Vec<usize> = lay
            .itape
            .ops
            .iter()
            .filter_map(|o| if let Op::Col(c, _) = o { Some(*c as usize) } else { None })
            .collect();
        cols.sort_unstable();
        cols.dedup();
        let apow = tab
            .interactions
            .iter()
            .map(|it| {
                let p: Vec<EF> = alpha.powers().take(it.msg.len() + 1).collect();
                let last = p[it.msg.len()] * F::from_u64(it.bus as u64 + 1);
                (p, last)
            })
            .collect();
        AuxSrc { main, tab, lay, pubs, alpha, gamma, cols, apow }
    }

    /// Interaction values and per-interaction data of row `r`: chain columns
    /// (`P_j`, `Π_j`, in layout order) and group factors `Φ_g`.
    #[allow(clippy::too_many_arguments)]
    fn row(&self, r: usize, need: &[bool], regs: &mut Vec<F>, cur: &mut Vec<F>, nxt: &mut Vec<F>, chain: &mut [EF], gphi: &mut [EF]) {
        let t = self.main.height();
        let w = self.main.width();
        cur.resize(w, F::ZERO);
        nxt.resize(w, F::ZERO);
        let nr = (r + 1) % t;
        for &c in &self.cols {
            cur[c] = self.main.get(r, c);
            nxt[c] = self.main.get(nr, c);
        }
        let sel = [
            if r == 0 { F::ONE } else { F::ZERO },
            if r + 1 == t { F::ONE } else { F::ZERO },
            if r + 1 == t { F::ZERO } else { F::ONE },
        ];
        self.lay.itape.eval::<F>(regs, |c, n| if n { nxt[c] } else { cur[c] }, self.pubs, sel);
        let mut phis = [EF::ONE; 64];
        let mut phis_v: Vec<EF>;
        let phis: &mut [EF] = if self.tab.interactions.len() <= 64 {
            &mut phis[..self.tab.interactions.len()]
        } else {
            phis_v = vec![EF::ONE; self.tab.interactions.len()];
            &mut phis_v
        };
        let outs = &self.lay.itape.outputs;
        for (ii, it) in self.tab.interactions.iter().enumerate() {
            if !need[ii] {
                continue;
            }
            let o = self.lay.expr_off[ii];
            let k = it.mult.len();
            if k <= 1 {
                // = γ − fingerprint(bus, msg, α) with base-field products
                let (ap, last) = &self.apow[ii];
                let mut fp = *last;
                for j in 0..it.msg.len() {
                    fp += ap[j] * regs[outs[o + j] as usize];
                }
                phis[ii] = if k == 0 { EF::ONE } else { EF::ONE + (self.gamma - fp - EF::ONE) * regs[outs[o + it.msg.len()] as usize] };
                continue;
            }
            let val = |k: usize| ef_from_base(regs[self.lay.itape.outputs[o + k] as usize]);
            let msg: Vec<EF> = (0..it.msg.len()).map(val).collect();
            let bits: Vec<EF> = (0..it.mult.len()).map(|k| val(it.msg.len() + k)).collect();
            let p0 = self.gamma - fingerprint(it.bus, &msg, self.alpha);
            let k = bits.len();
            phis[ii] = match k {
                0 => EF::ONE,
                1 => EF::ONE + bits[0] * (p0 - EF::ONE),
                _ => {
                    let off = self.lay.chain[ii].1;
                    let mut p = p0;
                    let mut pi = EF::ONE + bits[0] * (p0 - EF::ONE);
                    for j in 0..k - 1 {
                        p = p * p;
                        chain[off + j] = p;
                        pi *= EF::ONE + bits[j + 1] * (p - EF::ONE);
                        chain[off + k - 1 + j] = pi;
                    }
                    pi
                }
            };
        }
        for (g, grp) in self.lay.groups.iter().enumerate() {
            gphi[g] = grp.iter().fold(EF::ONE, |a, &i| a * phis[i]);
        }
    }

    /// Per-row chain values and group factors for rows `r0..r1`.
    /// Interactions needed for aux EF columns `e0..e1` (all for `None`).
    fn needed(&self, range: Option<(usize, usize)>) -> Vec<bool> {
        let n = self.tab.interactions.len();
        let Some((e0, e1)) = range else { return vec![true; n] };
        let nc = self.lay.n_chain;
        let mut need = vec![false; n];
        for ii in 0..n {
            let (k, off) = self.lay.chain[ii];
            if k >= 2 && off < e1 && off + 2 * (k - 1) > e0 {
                need[ii] = true;
            }
        }
        for (g, grp) in self.lay.groups.iter().enumerate() {
            if nc + g >= e0 && nc + g < e1 {
                for &i in grp {
                    need[i] = true;
                }
            }
        }
        need
    }

    fn rows(&self, r0: usize, r1: usize, need: &[bool]) -> (Vec<EF>, Vec<EF>) {
        let nc = self.lay.n_chain;
        let ng = self.lay.groups.len();
        let mut chains = vec![EF::ZERO; (r1 - r0) * nc];
        let mut phis = vec![EF::ONE; (r1 - r0) * ng];
        let (mut regs, mut cur, mut nxt) = (vec![], vec![], vec![]);
        for r in r0..r1 {
            let i = r - r0;
            self.row(r, need, &mut regs, &mut cur, &mut nxt, &mut chains[i * nc..(i + 1) * nc], &mut phis[i * ng..(i + 1) * ng]);
        }
        (chains, phis)
    }

    /// Values on `H` of the interaction expressions `o0..o1` (itape outputs),
    /// `T × (o1-o0)`. Every interaction expression has degree ≤ 1, so these
    /// determine the expressions' polynomials (of degree `< T`) everywhere.
    pub fn ivals(&self, o0: usize, o1: usize) -> RowMajorMatrix<F> {
        let _t = std::time::Instant::now();
        let t = self.main.height();
        let w = self.main.width();
        let cw = o1 - o0;
        let mut out = vec![F::ZERO; t * cw];
        if cw > 0 {
            out.par_chunks_mut(RCH * cw).enumerate().for_each(|(k, o)| {
                let (mut regs, mut cur, mut nxt) = (vec![], vec![F::ZERO; w], vec![F::ZERO; w]);
                for (i, orow) in o.chunks_mut(cw).enumerate() {
                    let r = k * RCH + i;
                    let nr = (r + 1) % t;
                    for &c in &self.cols {
                        cur[c] = self.main.get(r, c);
                        nxt[c] = self.main.get(nr, c);
                    }
                    let sel = [
                        if r == 0 { F::ONE } else { F::ZERO },
                        if r + 1 == t { F::ONE } else { F::ZERO },
                        if r + 1 == t { F::ZERO } else { F::ONE },
                    ];
                    self.lay.itape.eval::<F>(&mut regs, |c, n| if n { nxt[c] } else { cur[c] }, self.pubs, sel);
                    for (j, x) in orow.iter_mut().enumerate() {
                        *x = regs[self.lay.itape.outputs[o0 + j] as usize];
                    }
                }
            });
        }
        crate::lowmem::prof::add(&crate::lowmem::prof::AUXV, _t);
        RowMajorMatrix::new(out, cw)
    }

    /// Bus finals: `∏_rows Φ_g` per group.
    pub fn finals(&self) -> Vec<EF> {
        let t = self.main.height();
        let ng = self.lay.groups.len();
        if ng == 0 {
            return vec![];
        }
        let need = self.needed(None);
        (0..t.div_ceil(RCH))
            .into_par_iter()
            .map(|k| {
                let (_, phis) = self.rows(k * RCH, ((k + 1) * RCH).min(t), &need);
                let mut p = vec![EF::ONE; ng];
                for row in phis.chunks(ng) {
                    for (a, b) in p.iter_mut().zip(row) {
                        *a *= *b;
                    }
                }
                p
            })
            .reduce(|| vec![EF::ONE; ng], |a, b| a.iter().zip(&b).map(|(x, y)| *x * *y).collect())
    }

    /// Values on `H` of base columns `c0..c1` (multiples of 8).
    pub fn values(&self, c0: usize, c1: usize) -> RowMajorMatrix<F> {
        let _t = std::time::Instant::now();
        let r = self.values_(c0, c1);
        crate::lowmem::prof::add(&crate::lowmem::prof::AUXV, _t);
        r
    }
    fn values_(&self, c0: usize, c1: usize) -> RowMajorMatrix<F> {
        assert!(c0 % 8 == 0 && c1 % 8 == 0);
        let t = self.main.height();
        let nc = self.lay.n_chain;
        let ng = self.lay.groups.len();
        let (e0, e1) = (c0 / 8, c1 / 8);
        let need = self.needed(Some((e0, e1)));
        let cw = c1 - c0;
        let mut out = vec![F::ZERO; t * cw];
        if cw == 0 {
            return RowMajorMatrix::new(out, 0);
        }
        // running-product groups in range need the exclusive prefix product
        let g0 = e0.max(nc) - nc;
        let g1 = e1.max(nc) - nc;
        let nblk = t.div_ceil(RCH);
        // pass 1: per block, chain values written directly, group products
        let blk_prod: Vec<Vec<EF>> = out
            .par_chunks_mut(RCH * cw)
            .enumerate()
            .map(|(k, o)| {
                let r0 = k * RCH;
                let r1 = ((k + 1) * RCH).min(t);
                let (chains, phis) = self.rows(r0, r1, &need);
                let mut prod = vec![EF::ONE; g1 - g0];
                for i in 0..r1 - r0 {
                    let orow = &mut o[i * cw..(i + 1) * cw];
                    for e in e0..e1.min(nc) {
                        orow[8 * (e - e0)..8 * (e - e0) + 8].copy_from_slice(ef_coeffs(&chains[i * nc + e]));
                    }
                    // within-block exclusive prefix (fixed up in pass 2)
                    for g in g0..g1 {
                        let e = nc + g;
                        orow[8 * (e - e0)..8 * (e - e0) + 8].copy_from_slice(ef_coeffs(&prod[g - g0]));
                        prod[g - g0] *= phis[i * ng + g];
                    }
                }
                prod
            })
            .collect();
        if g1 > g0 {
            // block offsets
            let mut offs = vec![vec![EF::ONE; g1 - g0]; nblk];
            for k in 1..nblk {
                for g in 0..g1 - g0 {
                    offs[k][g] = offs[k - 1][g] * blk_prod[k - 1][g];
                }
            }
            out.par_chunks_mut(RCH * cw).enumerate().for_each(|(k, o)| {
                if k == 0 {
                    return;
                }
                for orow in o.chunks_mut(cw) {
                    for g in g0..g1 {
                        let e = nc + g;
                        let s = &mut orow[8 * (e - e0)..8 * (e - e0) + 8];
                        let v = EF::from_basis_coefficients_fn(|i| s[i]) * offs[k][g - g0];
                        s.copy_from_slice(ef_coeffs(&v));
                    }
                }
            });
        }
        RowMajorMatrix::new(out, cw)
    }
}
