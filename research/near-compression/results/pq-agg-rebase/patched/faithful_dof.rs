//! NV-faithful degree-of-freedom check (results/pq-recursion-nv/FAITHFUL.md §4).
//!
//! For an honest NV trace set, every cell of every AIR is perturbed one at a time
//! (v -> v + d, d a random non-zero field element) and the perturbation is classified:
//! * `constraint`: some AIR constraint is non-zero on one of the two windows (r-1, r), (r, r+1)
//!   that contain the cell;
//! * `bus`: the multiset of interactions changes, i.e. for some (bus, message) the net count
//!   over the affected windows changes.  Since the honest trace balances every bus exactly
//!   (checked first), a non-zero net change means the perturbed trace fails the bus argument
//!   (as an exact multiset statement; the LogUp error is accounted separately);
//! * `undetected`: neither.  Undetected cells are reported grouped by (AIR, row role, column).
//!
//! A second pass ("memory-coupled") perturbs, for free-result ALU ops, the result c_k of row y
//! together with every memory read of address y (operands a/b of the readers, E1/E2 copies),
//! which is the minimal consistent change of a memory cell, and reports which ops accept it.
use core::borrow::Borrow;
use std::collections::{BTreeMap, HashMap};

use openvm_stark_backend::{
    interaction::{BusIndex, Interaction, InteractionBuilder},
    AirRef,
};
use p3_air::{AirBuilder, AirBuilderWithPublicValues};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::{
    dense::{RowMajorMatrix, RowMajorMatrixView},
    stack::VerticalPair,
    Matrix,
};
use p3_maybe_rayon::prelude::*;

use super::{
    glue::GlueCols,
    isa::{Op, OP_HI, OP_LO},
    transcript2::{Hash2Cols, Samp2Cols},
    uair::{AbCols, BindCols, NvCommon, AB_W, BIND_W, N_COMMON, NV_WIDTH, POOL},
};
use crate::sha384::config::{Sha384Config, F};

/// Concrete-value builder over one window (local, next).
pub struct WinEval<'a> {
    pub main: VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>,
    pub pvs: &'a [F],
    pub first: F,
    pub last: F,
    pub trans: F,
    pub bad: usize,
    pub ints: Vec<Interaction<F>>,
}

impl<'a> AirBuilder for WinEval<'a> {
    type F = F;
    type Expr = F;
    type Var = F;
    type M = VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>;
    fn main(&self) -> Self::M {
        self.main
    }
    fn is_first_row(&self) -> F {
        self.first
    }
    fn is_last_row(&self) -> F {
        self.last
    }
    fn is_transition_window(&self, size: usize) -> F {
        assert_eq!(size, 2);
        self.trans
    }
    fn assert_zero<I: Into<F>>(&mut self, x: I) {
        if x.into() != F::ZERO {
            self.bad += 1;
        }
    }
}
// the DOF harness evaluates the unpartitioned NvAir (program in common main)
impl<'a> openvm_stark_backend::air_builders::PartitionedAirBuilder for WinEval<'a> {
    fn cached_mains(&self) -> &[Self::M] {
        &[]
    }
    fn common_main(&self) -> &Self::M {
        &self.main
    }
}
impl<'a> InteractionBuilder for WinEval<'a> {
    fn push_interaction<E: Into<F>>(&mut self, bus_index: BusIndex, fields: impl IntoIterator<Item = E>, count: impl Into<F>, count_weight: u32) {
        self.ints.push(Interaction { message: fields.into_iter().map(Into::into).collect(), count: count.into(), bus_index, count_weight });
    }
    fn num_interactions(&self) -> usize {
        self.ints.len()
    }
    fn all_interactions(&self) -> &[Interaction<F>] {
        &self.ints
    }
}
impl<'a> AirBuilderWithPublicValues for WinEval<'a> {
    type PublicVar = F;
    fn public_values(&self) -> &[F] {
        self.pvs
    }
}

pub type Key = (BusIndex, Vec<u32>);

/// Evaluate window r of `m` (rows r, r+1 mod h): (#non-zero constraints, interactions).
pub fn eval_window(air: &AirRef<Sha384Config>, m: &RowMajorMatrix<F>, r: usize, pvs: &[F]) -> (usize, Vec<Interaction<F>>) {
    let h = m.height();
    let w = m.width();
    let rn = (r + 1) % h;
    let local = &m.values[r * w..(r + 1) * w];
    let next = &m.values[rn * w..(rn + 1) * w];
    eval_rows(air, local, next, r == 0, r + 1 == h, pvs)
}

pub fn eval_rows(air: &AirRef<Sha384Config>, local: &[F], next: &[F], first: bool, last: bool, pvs: &[F]) -> (usize, Vec<Interaction<F>>) {
    let mut b = WinEval {
        main: VerticalPair::new(RowMajorMatrixView::new_row(local), RowMajorMatrixView::new_row(next)),
        pvs,
        first: F::from_bool(first),
        last: F::from_bool(last),
        trans: F::from_bool(!last),
        bad: 0,
        ints: vec![],
    };
    eval_any(air, &mut b);
    (b.bad, b.ints)
}

/// Dispatch to the concrete AIR types of the NV circuit.
fn eval_any(air: &AirRef<Sha384Config>, b: &mut WinEval) {
    use p3_air::Air;
    let any = air.as_any();
    if let Some(a) = any.downcast_ref::<super::uair::NvAir>() {
        a.eval(b)
    } else if let Some(a) = any.downcast_ref::<crate::sha384::compress4_air::Sha512Air4>() {
        a.eval(b)
    } else if let Some(a) = any.downcast_ref::<crate::sha384::compress4_air::TableAir4>() {
        a.eval(b)
    } else if let Some(a) = any.downcast_ref::<super::hash::ByteAir>() {
        a.eval(b)
    } else {
        panic!("unknown AIR {}", air.name())
    }
}

pub fn add_ints(acc: &mut HashMap<Key, F>, ints: &[Interaction<F>], sign: F) {
    for it in ints {
        if it.count == F::ZERO {
            continue;
        }
        let k = (it.bus_index, it.message.iter().map(|x| x.as_canonical_u32()).collect());
        *acc.entry(k).or_insert(F::ZERO) += sign * it.count;
    }
}

/// Global check of the honest trace with this evaluator: all constraints zero, all buses balanced.
pub fn global_check(airs: &[AirRef<Sha384Config>], mats: &[RowMajorMatrix<F>], pvs: &[Vec<F>]) -> (usize, usize) {
    let mut bad = 0;
    let mut acc: HashMap<Key, F> = HashMap::new();
    for (i, (a, m)) in airs.iter().zip(mats).enumerate() {
        let per: Vec<(usize, Vec<Interaction<F>>)> = (0..m.height()).into_par_iter().map(|r| eval_window(a, m, r, &pvs[i])).collect();
        for (bd, ints) in per {
            bad += bd;
            add_ints(&mut acc, &ints, F::ONE);
        }
    }
    let unbalanced = acc.values().filter(|v| **v != F::ZERO).count();
    (bad, unbalanced)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Constraint,
    Bus,
    Undetected,
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn nz(&mut self) -> F {
        loop {
            let v = (self.next() % 2013265921) as u32;
            if v != 0 {
                return F::from_u32(v);
            }
        }
    }
}

/// Perturb cell (r, c) of matrix `m` by `d`; classify.
pub fn perturb(air: &AirRef<Sha384Config>, m: &RowMajorMatrix<F>, r: usize, c: usize, d: F, pvs: &[F]) -> Verdict {
    let h = m.height();
    let w = m.width();
    let mut wins = vec![r];
    if h > 1 {
        wins.push((r + h - 1) % h);
    }
    wins.dedup();
    let mut delta: HashMap<Key, F> = HashMap::new();
    let mut bad = 0;
    for &x in &wins {
        let (_, ints) = eval_window(air, m, x, pvs);
        add_ints(&mut delta, &ints, -F::ONE);
        let xn = (x + 1) % h;
        let mut local = m.values[x * w..(x + 1) * w].to_vec();
        let mut next = m.values[xn * w..(xn + 1) * w].to_vec();
        if x == r {
            local[c] += d;
        }
        if xn == r {
            next[c] += d;
        }
        let (bd, ints) = eval_rows(air, &local, &next, x == 0, x + 1 == h, pvs);
        bad += bd;
        add_ints(&mut delta, &ints, F::ONE);
    }
    if bad > 0 {
        Verdict::Constraint
    } else if delta.values().any(|v| *v != F::ZERO) {
        Verdict::Bus
    } else {
        Verdict::Undetected
    }
}

/// Column names of NvAir for a given role.
pub fn nv_col_names(role: &str) -> Vec<String> {
    let mut n: Vec<String> = (0..NV_WIDTH).map(|i| if i < N_COMMON { String::new() } else { format!("pool{}", i - N_COMMON) }).collect();
    let idx: Vec<usize> = (0..NV_WIDTH).collect();
    let cm: &NvCommon<usize> = idx[..N_COMMON].borrow();
    for (s, v) in [("ka", cm.ka), ("kb", cm.kb), ("kg", cm.kg), ("kh", cm.kh), ("ks", cm.ks), ("y", cm.y)] {
        n[v] = s.into();
    }
    for j in 0..4 {
        n[cm.p[j]] = format!("P{j}");
    }
    // columns inside the role's view are "v<i>" until named below; only columns beyond the view
    // are "pool<i>" (the don't-care class "beyond the role view" must not hide unnamed columns)
    let view = match role {
        r if r.starts_with("ALU") => AB_W,
        "BIND" => BIND_W,
        r if r.starts_with("GLUE") => super::glue::GLUE_W,
        r if r.starts_with("HASH") => super::transcript2::HASH2_WIDTH,
        r if r.starts_with("SAMP") => super::transcript2::SAMP2_WIDTH,
        _ => 0,
    };
    for i in 0..view {
        n[N_COMMON + i] = format!("v{i}");
    }
    let pool = &idx[N_COMMON..];
    let mut set = |i: usize, s: String| n[i] = s;
    match role {
        r if r.starts_with("ALU") => {
            let c: &AbCols<usize> = pool[..AB_W].borrow();
            for k in 0..12 {
                set(c.a[k], format!("a{k}"));
                set(c.b[k], format!("b{k}"));
                set(c.c[k], format!("c{k}"));
            }
            for k in 0..OP_LO {
                set(c.h[k], format!("h{k}"));
            }
            for k in 0..OP_HI {
                set(c.g[k], format!("g{k}"));
            }
            set(c.wit, "wit".into());
            set(c.wit2, "wit2".into());
            set(c.mult, "mult".into());
            set(c.rx, "rx".into());
            set(c.ry, "ry".into());
            set(c.rz, "rz".into());
        }
        "BIND" => {
            let c: &BindCols<usize> = pool[..BIND_W].borrow();
            for k in 0..12 {
                set(c.e1a[k], format!("e1a{k}"));
                set(c.e1b[k], format!("e1b{k}"));
                set(c.e2[k], format!("e2{k}"));
                set(c.acc[k], format!("acc{k}"));
            }
            for j in 0..4 {
                set(c.pc0[j], format!("pc0_{j}"));
                set(c.pc1[j], format!("pc1_{j}"));
            }
            set(c.ya, "ya".into());
            set(c.yb, "yb".into());
            set(c.bl, "bl".into());
        }
        r if r.starts_with("GLUE") => {
            let c: &GlueCols<usize> = pool[..super::glue::GLUE_W].borrow();
            for (s, v) in [("start", c.start), ("job", c.job), ("cid", c.cid), ("blk0", c.blk0), ("last", c.last), ("end", c.end), ("act", c.act), ("phase", c.phase), ("uidx", c.uidx), ("carry", c.carry), ("nd", c.nd), ("carry2", c.carry2), ("lo6", c.lo6), ("tr", c.tr), ("hp", c.hp), ("hs", c.hs)] {
                set(v, s.into());
            }
            for k in 0..3 {
                set(c.q[k], format!("q{k}"));
            }
            for k in 0..16 {
                set(c.b[k], format!("b{k}"));
            }
            for k in 0..4 {
                set(c.lo[k], format!("lo{k}"));
                set(c.ulo[k], format!("ulo{k}"));
                set(c.p[k], format!("p{k}"));
                set(c.zm[k], format!("zm{k}"));
            }
            for k in 0..2 {
                set(c.wd[k], format!("wd{k}"));
            }
            for k in 0..6 {
                set(c.s[k], format!("s{k}"));
            }
        }
        r if r.starts_with("HASH") => {
            let c: &Hash2Cols<usize> = pool[..super::transcript2::HASH2_WIDTH].borrow();
            for (s, v) in [("is_first", c.is_first), ("op_f", c.op_f), ("op_c", c.op_c), ("op_s", c.op_s), ("op_p", c.op_p), ("job", c.job), ("nxt", c.nxt), ("hn", c.hn), ("t_start", c.t_start), ("cnt", c.cnt), ("last_word", c.last_word), ("last_half", c.last_half), ("last_acc", c.last_acc), ("full", c.full), ("ns", c.ns), ("op_q", c.op_q), ("scnt", c.scnt), ("ctr", c.ctr), ("nwit", c.nwit), ("rd", c.rd), ("nsq", c.nsq), ("nq", c.nq), ("w0", c.w[0]), ("w1", c.w[1])] {
                set(v, s.into());
            }
            for (k, &v) in c.state_out.iter().enumerate() {
                set(v, format!("state_out{k}"));
            }
            for (k, &v) in c.state_in.iter().enumerate() {
                set(v, format!("state_in{k}"));
            }
            for k in 0..6 {
                set(c.rdw[k], format!("rdw{k}"));
            }
        }
        "SAMP" => {
            let c: &Samp2Cols<usize> = pool[..super::transcript2::SAMP2_WIDTH].borrow();
            for (s, v) in [("job", c.job), ("wi", c.wi), ("t_job", c.t_job), ("mbefore", c.mbefore), ("is_first", c.is_first), ("is_last", c.is_last), ("lo5", c.lo5), ("lo2", c.lo2), ("h1", c.h1)] {
                set(v, s.into());
            }
            for k in 0..8 {
                set(c.b[k], format!("b{k}"));
            }
            for k in 0..2 {
                for (s, a) in [("g", c.g), ("z", c.z), ("iz", c.iz), ("zv", c.zv), ("iv", c.iv), ("zc", c.zc), ("ic", c.ic), ("acc", c.acc)] {
                    set(a[k], format!("{s}{k}"));
                }
            }
        }
        _ => {}
    }
    let _ = POOL;
    n
}

/// Role of NvAir row r.
pub fn nv_role(m: &RowMajorMatrix<F>, r: usize) -> String {
    let w = m.width();
    let row = &m.values[r * w..(r + 1) * w];
    let idx: Vec<usize> = (0..NV_WIDTH).collect();
    let cm: &NvCommon<usize> = idx[..N_COMMON].borrow();
    if row[cm.ka] == F::ONE {
        let c: &AbCols<usize> = idx[N_COMMON..N_COMMON + AB_W].borrow();
        let lo = (0..OP_LO).find(|&k| row[c.h[k]] == F::ONE).unwrap_or(99);
        let hi = (0..OP_HI).find(|&k| row[c.g[k]] == F::ONE).unwrap_or(99);
        let v = 8 * hi + lo;
        let name = Op::all().into_iter().find(|o| *o as usize == v).map_or(format!("op{v}"), |o| format!("{o:?}"));
        return format!("ALU:{name}");
    }
    if row[cm.kb] == F::ONE {
        return "BIND".into();
    }
    if row[cm.kg] == F::ONE {
        let c: &GlueCols<usize> = idx[N_COMMON..N_COMMON + super::glue::GLUE_W].borrow();
        let q = (0..3).map(|k| (row[c.q[k]].as_canonical_u32() as usize) << k).sum::<usize>();
        let nd = row[c.nd] == F::ONE;
        let pos = if row[c.end] == F::ONE { "end" } else if row[c.last] == F::ONE { "last" } else { "mid" };
        return format!("GLUE{}:q{q}:{pos}", if nd { "-node" } else { "" });
    }
    if row[cm.kh] == F::ONE {
        let c: &Hash2Cols<usize> = idx[N_COMMON..N_COMMON + super::transcript2::HASH2_WIDTH].borrow();
        let op = [(c.op_f, "f"), (c.op_c, "c"), (c.op_s, "s"), (c.op_p, "p"), (c.op_q, "q")]
            .iter()
            .find(|(i, _)| row[*i] == F::ONE)
            .map_or("?", |x| x.1);
        return if row[c.hn] == F::ONE { format!("HASH:{op}") } else { format!("HASH:{op}:hn0") };
    }
    if row[cm.ks] == F::ONE {
        return "SAMP".into();
    }
    "PAD".into()
}

/// SAMP is-zero gadgets: x * inv = 1 - z, z * x = 0.  For x = 0 the inverse column is free.
pub fn samp_inverse_operand_zero(m: &RowMajorMatrix<F>, r: usize, col: &str) -> bool {
    let w = m.width();
    let row = &m.values[r * w + N_COMMON..(r + 1) * w];
    let idx: Vec<usize> = (0..super::transcript2::SAMP2_WIDTH).collect();
    let c: &Samp2Cols<usize> = idx[..].borrow();
    let h: usize = match col.get(2..).and_then(|x| x.parse().ok()) {
        Some(h) if h < 2 => h,
        _ => return false,
    };
    let cb: Vec<u64> = (0..4).map(|k| row[c.b[4 * h + k]].as_canonical_u32() as u64).collect();
    let x = match &col[..2] {
        "iz" => F::from_u64(cb[3]) - F::from_u32(0xF0),
        "iv" => F::from_u64(cb[1] << 8 | cb[2] << 16),
        "ic" => F::from_u64(cb[0] * cb[0]) - F::from_u64(cb[0]),
        _ => return false,
    };
    x == F::ZERO
}

#[derive(Default, Debug, Clone)]
pub struct Tally {
    pub tested: usize,
    pub constraint: usize,
    pub bus: usize,
    pub undetected: usize,
    pub example_row: usize,
}

/// Run the full single-cell perturbation; returns per (air, role, column) tallies.
/// `row_cap`: at most this many rows per (air, role) are perturbed (all columns); None = all.
pub fn run_dof(airs: &[AirRef<Sha384Config>], mats: &[RowMajorMatrix<F>], pvs: &[Vec<F>], row_cap: Option<usize>, seed: u64) -> BTreeMap<(String, String, String), Tally> {
    let mut out: BTreeMap<(String, String, String), Tally> = BTreeMap::new();
    for (i, (a, m)) in airs.iter().zip(mats).enumerate() {
        let h = m.height();
        let w = m.width();
        let aname = a.name();
        let role_of = |r: usize| -> String {
            if i == 0 {
                nv_role(m, r)
            } else if i == 1 {
                // SHA compression AIR: row within the 128-row compression, padding if all-zero
                let zero = m.values[r * w..(r + 1) * w].iter().all(|v| *v == F::ZERO);
                if zero { "PAD".into() } else { format!("sha_row{}", r % crate::sha384::compress4_air::ROWS) }
            } else if i == 3 && m.values[r * w] == F::from_u32(255) {
                "x255".into()
            } else {
                "row".into()
            }
        };
        // choose rows: per role, up to row_cap rows spread over the region (first, last, random)
        let roles: Vec<String> = (0..h).map(role_of).collect();
        let mut by_role: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for (r, ro) in roles.iter().enumerate() {
            by_role.entry(ro.clone()).or_default().push(r);
        }
        let mut rows: Vec<usize> = vec![];
        for (_, rs) in by_role.iter() {
            match row_cap {
                Some(cap) if rs.len() > cap => {
                    let mut rng = Rng(seed ^ (rs[0] as u64));
                    let mut pick = vec![rs[0], rs[rs.len() - 1]];
                    while pick.len() < cap {
                        pick.push(rs[(rng.next() % rs.len() as u64) as usize]);
                    }
                    pick.sort();
                    pick.dedup();
                    rows.extend(pick);
                }
                _ => rows.extend(rs.iter().copied()),
            }
        }
        let names_cache: HashMap<String, Vec<String>> = if i == 0 {
            by_role.keys().map(|ro| (ro.clone(), nv_col_names(ro))).collect()
        } else {
            HashMap::new()
        };
        let res: Vec<(usize, usize, Verdict)> = rows
            .par_iter()
            .flat_map_iter(|&r| {
                let mut rng = Rng(seed.wrapping_mul(31).wrapping_add((i as u64) << 40).wrapping_add(r as u64));
                (0..w).map(move |c| (r, c, rng.nz())).collect::<Vec<_>>()
            })
            .map(|(r, c, d)| (r, c, perturb(a, m, r, c, d, &pvs[i])))
            .collect();
        for (r, c, v) in res {
            let mut ro = roles[r].clone();
            let cname = if i == 0 { names_cache[&ro][c].clone() } else { format!("c{c}") };
            if i == 0 && ro == "SAMP" && v == Verdict::Undetected && samp_inverse_operand_zero(m, r, &cname) {
                ro = "SAMP:inv-operand-0".into();
            }
            let t = out.entry((aname.clone(), ro, cname)).or_default();
            t.tested += 1;
            match v {
                Verdict::Constraint => t.constraint += 1,
                Verdict::Bus => t.bus += 1,
                Verdict::Undetected => {
                    if t.undetected == 0 {
                        t.example_row = r;
                    }
                    t.undetected += 1
                }
            }
        }
    }
    out
}

/// Memory-coupled perturbation of ALU row y, coefficient k: c_k[y] += d and every read of
/// address y (a_k / b_k of reader rows, e1a/e1b/e2 copies in BIND/app rows) += d.
/// Returns true if the perturbed trace still satisfies every constraint and bus.
pub fn mem_coupled(air: &AirRef<Sha384Config>, m: &RowMajorMatrix<F>, readers: &[(usize, usize)], y: usize, k: usize, d: F, pvs: &[F]) -> bool {
    // readers: (row, column) cells holding a copy of c_k[y]
    let w = m.width();
    let h = m.height();
    let c_col = N_COMMON + core::mem::offset_of!(super::uair::AbCols<u8>, c) + k;
    let mut cells = vec![(y, c_col)];
    cells.extend(readers.iter().copied());
    let mut wins: Vec<usize> = cells.iter().flat_map(|&(r, _)| [r, (r + h - 1) % h]).collect();
    wins.sort();
    wins.dedup();
    let row_of = |x: usize| -> Vec<F> {
        let mut v = m.values[x * w..(x + 1) * w].to_vec();
        for &(r, c) in &cells {
            if r == x {
                v[c] += d;
            }
        }
        v
    };
    let mut delta: HashMap<Key, F> = HashMap::new();
    for &x in &wins {
        let (_, ints) = eval_window(air, m, x, pvs);
        add_ints(&mut delta, &ints, -F::ONE);
        let (bd, ints) = eval_rows(air, &row_of(x), &row_of((x + 1) % h), x == 0, x + 1 == h, pvs);
        if bd > 0 {
            return false;
        }
        add_ints(&mut delta, &ints, F::ONE);
    }
    delta.values().all(|v| *v == F::ZERO)
}
