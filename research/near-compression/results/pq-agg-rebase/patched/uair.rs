//! NV merged non-SHA AIR ("NvAir", U2): one AIR, row roles sharing a column pool.
//!
//! Common columns: role flags ka (ALU), kb (BIND), kg (GLUE), kh (transcript hash chain),
//! ks (sample), the row index y and the program words P0..P3 (zero off ALU rows).
//! Pool: the role's view (AbCols for ALU / BIND, GlueCols, Hash2Cols, Samp2Cols).
//! Rows are ordered by role: ALU [0, 2^prog_log), BIND (one per ALU row), GLUE, HASH,
//! SAMP, padding (no role); the order is enforced by a monotone stage.
//!
//! * ALU rows: one Ext12 instruction (isa.rs) per row; row y writes c at memory address
//!   y.  Op = 8 * hi + lo with one-hot halves h[8] (lo), g[3] (hi); selector(op) =
//!   ka * h[lo] * g[hi].  Every ALU row sends (y, P0..P3) on the bind bus.
//! * BIND rows: row for ALU row y = ya + 512 yb holds e1 = E1[ya], e2 = E2[yb] (read from
//!   memory: the program's reserved rows [0, 512) and [512, 512 + 2^(prog_log - 9))),
//!   receives (y, P0..P3) and accumulates acc += e1 * e2 * sum_j tau^j P_j; the last BIND
//!   row sends the total to the ALU `Acc` row.  P is zero outside ALU rows, so the total
//!   is the multilinear evaluation of the program columns over the whole trace.
//!   Shared pool columns: a|e1, b|e2, c|acc, h[0..4]|pc0..3, h[4]|ya, h[5]|yb, h[6]|zw,
//!   h[7]|inv_w, wit|bf (first BIND row), mult|bl (last BIND row).
//!
//! Each role is evaluated against a collecting builder; interactions of different roles
//! on the same bus are merged into shared slots (message = sum_role flag * message,
//! count = sum of the role-gated counts).
use core::borrow::{Borrow, BorrowMut};
use std::collections::BTreeMap;

use openvm_recursion_circuit_derive::AlignedBorrow;
use openvm_stark_backend::{
    air_builders::PartitionedAirBuilder,
    interaction::{BusIndex, Interaction, InteractionBuilder, LookupBus, PermutationCheckBus},
    BaseAirWithPublicValues, PartitionedBaseAir,
};
use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing};
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use super::{
    glue::{eval_glue, GlueCols, GLUE_W},
    hash::HashBuses,
    isa::{Instr, Op, ADDR_BITS, OP_HI, OP_LO},
    transcript2::{eval_hash, eval_samp, Hash2Cols, Samp2Cols, TrBuses, HASH2_WIDTH, SAMP2_WIDTH},
};
use crate::{
    sha384::config::{EF, F, KIND_SAMPLE},
    utils::{ext_field_add, ext_field_multiply},
};

/// Binding tables: E1 over the low E1_BITS row bits, E2 over the rest.
pub const E1_BITS: usize = 9;
pub const E1_SIZE: usize = 1 << E1_BITS;

/// Binding constant tau = X + 1 (any element outside F works; see DESIGN.md).
pub fn tau() -> EF {
    let mut c = [F::ZERO; 12];
    c[0] = F::ONE;
    c[1] = F::ONE;
    EF::from_basis_coefficients_slice(&c).unwrap()
}
pub fn tau_pows() -> [EF; 4] {
    let t = tau();
    [EF::ONE, t, t * t, t * t * t]
}

#[derive(Clone, Copy, Debug)]
pub struct UBuses {
    pub mem: BusIndex,
    pub slot: BusIndex,
    pub job: BusIndex,
    pub digest: BusIndex,
    pub bind: BusIndex,
    pub acc: BusIndex,
}

#[repr(C)]
#[derive(AlignedBorrow, Debug)]
pub struct NvCommon<T> {
    pub ka: T,
    pub kb: T,
    pub kg: T,
    pub kh: T,
    pub ks: T,
    pub y: T,
    /// program words P0..P3
    pub p: [T; 4],
}
pub const N_COMMON: usize = NvCommon::<u8>::width();

#[repr(C)]
#[derive(AlignedBorrow, Debug)]
pub struct AbCols<T> {
    pub a: [T; 12],
    pub b: [T; 12],
    pub h: [T; OP_LO],
    pub wit: T,
    pub mult: T,
    /// bytes of the B field: B = rx + 256 ry + 65536 rz, three bytes (binds the op to P1)
    pub rx: T,
    pub ry: T,
    /// the result: pool 36..48, the positions of BIND's accumulator, which are already opened at
    /// the next row (the Horner ops read the next row's c at no extra opening)
    pub c: [T; 12],
    pub g: [T; OP_HI],
    pub rz: T,
    /// Horn2's second base witness
    pub wit2: T,
}
const _: () = assert!(core::mem::offset_of!(AbCols<u8>, c) == 36 && core::mem::offset_of!(BindCols<u8>, acc) == 36);
pub const AB_W: usize = AbCols::<u8>::width();

#[repr(C)]
#[derive(AlignedBorrow, Debug)]
pub struct BindCols<T> {
    /// E1[ya], E1[ya + 1], E2[yb]
    pub e1a: [T; 12],
    pub e1b: [T; 12],
    pub e2: [T; 12],
    /// accumulator before this row
    pub acc: [T; 12],
    /// program words of ALU rows 2t, 2t + 1
    pub pc0: [T; 4],
    pub pc1: [T; 4],
    pub ya: T,
    pub yb: T,
    /// last BIND row
    pub bl: T,
}
pub const BIND_W: usize = BindCols::<u8>::width();

const fn max(a: usize, b: usize) -> usize {
    if a > b {
        a
    } else {
        b
    }
}
pub const POOL: usize = max(max(max(AB_W, BIND_W), GLUE_W), max(HASH2_WIDTH, SAMP2_WIDTH));
pub const NV_WIDTH: usize = N_COMMON + POOL;
/// Column offsets used by tests / the binding check.
pub const U_P: usize = core::mem::offset_of!(NvCommon<u8>, p);
/// NvAir public values: [level, statement digest limbs (18)]
pub const NV_NUM_PVS: usize = 1 + super::fmt::NV_DIGEST;
pub const U_A: usize = N_COMMON;
pub const U_C: usize = N_COMMON + 36;

pub struct NvAir {
    pub buses: UBuses,
    pub h: HashBuses,
    pub t: TrBuses,
    /// G2: the program columns P0..P3 form a separate CACHED main part (one commitment per
    /// level, the program's; its root is a proof value bound by the parent: C_L1 for a level-1
    /// child, BIND otherwise).  FINAL keeps them in common main (one commitment).
    pub program_part: bool,
}
/// Number of program columns (the cached part when `program_part`).
pub const N_PROG: usize = 4;
impl<T> BaseAir<T> for NvAir {
    fn width(&self) -> usize {
        NV_WIDTH
    }
}
impl<T> BaseAirWithPublicValues<T> for NvAir {
    fn num_public_values(&self) -> usize {
        NV_NUM_PVS
    }
}
impl<T> PartitionedBaseAir<T> for NvAir {
    fn cached_main_widths(&self) -> Vec<usize> {
        if self.program_part {
            vec![N_PROG]
        } else {
            vec![]
        }
    }
    fn common_main_width(&self) -> usize {
        if self.program_part {
            NV_WIDTH - N_PROG
        } else {
            NV_WIDTH
        }
    }
}

/// Split an NvAir trace into (common main without P0..P3, the program part P0..P3).
pub fn split_program_part(m: &RowMajorMatrix<F>) -> (RowMajorMatrix<F>, RowMajorMatrix<F>) {
    let w = m.width;
    assert_eq!(w, NV_WIDTH);
    let h = m.values.len() / w;
    let mut common = Vec::with_capacity(h * (w - N_PROG));
    let mut prog = Vec::with_capacity(h * N_PROG);
    for r in 0..h {
        let row = &m.values[r * w..(r + 1) * w];
        common.extend_from_slice(&row[..U_P]);
        common.extend_from_slice(&row[U_P + N_PROG..]);
        prog.extend_from_slice(&row[U_P..U_P + N_PROG]);
    }
    (RowMajorMatrix::new(common, w - N_PROG), RowMajorMatrix::new(prog, N_PROG))
}

/// Builder adapter: constraints go to the inner builder, interactions are collected.
pub struct Collect<'a, AB: InteractionBuilder> {
    pub inner: &'a mut AB,
    pub ints: Vec<Interaction<AB::Expr>>,
}
impl<'a, AB: InteractionBuilder> AirBuilder for Collect<'a, AB> {
    type F = AB::F;
    type Expr = AB::Expr;
    type Var = AB::Var;
    type M = AB::M;
    fn main(&self) -> Self::M {
        self.inner.main()
    }
    fn is_first_row(&self) -> Self::Expr {
        self.inner.is_first_row()
    }
    fn is_last_row(&self) -> Self::Expr {
        self.inner.is_last_row()
    }
    fn is_transition_window(&self, size: usize) -> Self::Expr {
        self.inner.is_transition_window(size)
    }
    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.inner.assert_zero(x)
    }
}
impl<'a, AB: InteractionBuilder> InteractionBuilder for Collect<'a, AB> {
    fn push_interaction<E: Into<Self::Expr>>(
        &mut self,
        bus_index: BusIndex,
        fields: impl IntoIterator<Item = E>,
        count: impl Into<Self::Expr>,
        count_weight: u32,
    ) {
        self.ints.push(Interaction {
            message: fields.into_iter().map(Into::into).collect(),
            count: count.into(),
            bus_index,
            count_weight,
        });
    }
    fn num_interactions(&self) -> usize {
        self.ints.len()
    }
    fn all_interactions(&self) -> &[Interaction<Self::Expr>] {
        &self.ints
    }
}
impl<'a, AB: InteractionBuilder + AirBuilderWithPublicValues> AirBuilderWithPublicValues for Collect<'a, AB> {
    type PublicVar = AB::PublicVar;
    fn public_values(&self) -> &[Self::PublicVar] {
        self.inner.public_values()
    }
}

/// Merge role interactions into shared slots per bus and push them.
fn merge_push<AB: InteractionBuilder>(builder: &mut AB, groups: Vec<(AB::Expr, Vec<Interaction<AB::Expr>>)>) {
    if std::env::var("NV_INT_DUMP").is_ok() {
        let mut t: BTreeMap<BusIndex, Vec<usize>> = BTreeMap::new();
        for (g, (_, ints)) in groups.iter().enumerate() {
            for it in ints {
                t.entry(it.bus_index).or_insert(vec![0; groups.len()])[g] += 1;
            }
        }
        for (bus, c) in t {
            eprintln!("NV_INT bus={bus} per-role [alu,bind,glue,hash,samp]={c:?} max={}", c.iter().max().unwrap());
        }
    }
    let mut slots: BTreeMap<BusIndex, Vec<Vec<(AB::Expr, Interaction<AB::Expr>)>>> = BTreeMap::new();
    for (flag, ints) in groups {
        let mut idx: BTreeMap<BusIndex, usize> = BTreeMap::new();
        for it in ints {
            let i = idx.entry(it.bus_index).or_default();
            let v = slots.entry(it.bus_index).or_default();
            if v.len() <= *i {
                v.push(vec![]);
            }
            v[*i].push((flag.clone(), it));
            *i += 1;
        }
    }
    if std::env::var("NV_INT_DUMP").is_ok() {
        for (bus, v) in &slots {
            let per: Vec<usize> = v.iter().map(|s| s.len()).collect();
            eprintln!("NV_INT bus={bus} slots={} (roles per slot {:?})", v.len(), per);
        }
    }
    for (bus, v) in slots {
        for slot in v {
            if slot.len() == 1 {
                let (_, it) = slot.into_iter().next().unwrap();
                builder.push_interaction(bus, it.message, it.count, it.count_weight);
                continue;
            }
            let len = slot[0].1.message.len();
            let mut msg = vec![AB::Expr::ZERO; len];
            let mut count = AB::Expr::ZERO;
            let mut weight = 0;
            for (flag, it) in slot {
                assert_eq!(it.message.len(), len, "bus {bus}: message lengths differ");
                for (m, f) in msg.iter_mut().zip(it.message) {
                    *m += flag.clone() * f;
                }
                count += it.count;
                weight = weight.max(it.count_weight);
            }
            builder.push_interaction(bus, msg, count, weight);
        }
    }
}

impl<AB: AirBuilderWithPublicValues + InteractionBuilder + PartitionedAirBuilder> Air<AB> for NvAir
where
    <AB::Expr as PrimeCharacteristicRing>::PrimeSubfield:
        p3_field::extension::BinomiallyExtendable<12>,
{
    fn eval(&self, builder: &mut AB) {
        // the full row view [common 0..7, P0..P3, common 7..]: P0..P3 come from the cached
        // program part when `program_part`
        let (local, next): (Vec<AB::Var>, Vec<AB::Var>) = if self.program_part {
            let cm = builder.common_main();
            let pm = &builder.cached_mains()[0];
            let row = |i: usize| -> Vec<AB::Var> {
                let c = cm.row_slice(i).unwrap();
                let p = pm.row_slice(i).unwrap();
                c[..U_P].iter().chain(p.iter()).chain(c[U_P..].iter()).copied().collect()
            };
            (row(0), row(1))
        } else {
            let main = builder.main();
            let (l, n) = (main.row_slice(0).unwrap(), main.row_slice(1).unwrap());
            (l.to_vec(), n.to_vec())
        };
        let cl: &NvCommon<AB::Var> = local[..N_COMMON].borrow();
        let cn: &NvCommon<AB::Var> = next[..N_COMMON].borrow();
        let pl = &local[N_COMMON..];
        let pn = &next[N_COMMON..];
        let one = AB::Expr::ONE;
        let kinds = [cl.ka, cl.kb, cl.kg, cl.kh, cl.ks];
        let mut ksum = AB::Expr::ZERO;
        for k in kinds {
            builder.assert_bool(k);
            ksum += k.into();
        }
        builder.assert_bool(ksum.clone());
        // y = row index on role rows; padding rows (no role, the last region) are all zero, so
        // all-zero rows satisfy the AIR (tight-heights lever: a zero tail is not committed)
        builder.when_first_row().assert_zero(cl.y);
        let npad: AB::Expr = cn.ka + cn.kb + cn.kg + cn.kh + cn.ks;
        builder.when_transition().assert_zero(npad * (cn.y - cl.y - one.clone()));
        builder.assert_zero((one.clone() - ksum.clone()) * cl.y);
        // padding rows are all zero (pool included), so a non-zero tail is rejected
        for &x in pl.iter() {
            builder.assert_zero((one.clone() - ksum.clone()) * x);
        }
        for j in 0..4 {
            builder.assert_zero((one.clone() - cl.ka) * cl.p[j]);
        }
        // role order: stage(ALU) = 0 < BIND < GLUE < HASH < SAMP < padding = 5, non-decreasing
        let stage = |c: &NvCommon<AB::Var>| -> AB::Expr {
            let s = c.ka + c.kb + c.kg + c.kh + c.ks;
            c.kb + c.kg * AB::Expr::TWO + c.kh * AB::Expr::from_u64(3) + c.ks * AB::Expr::from_u64(4)
                + (one.clone() - s) * AB::Expr::from_u64(5)
        };
        let d = stage(cn) - stage(cl);
        let mut poly = AB::Expr::ONE;
        for i in 0..6u64 {
            poly = poly * (d.clone() - AB::Expr::from_u64(i));
        }
        builder.when_transition().assert_zero(poly);

        let mut groups = vec![];
        {
            let l: &AbCols<AB::Var> = pl[..AB_W].borrow();
            let n: &AbCols<AB::Var> = pn[..AB_W].borrow();
            let mut cb = Collect { inner: &mut *builder, ints: vec![] };
            eval_alu(&mut cb, cl, l, n, &self.buses, self.h.byte);
            groups.push((cl.ka.into(), cb.ints));
        }
        {
            let l: &BindCols<AB::Var> = pl[..BIND_W].borrow();
            let n: &BindCols<AB::Var> = pn[..BIND_W].borrow();
            let mut cb = Collect { inner: &mut *builder, ints: vec![] };
            eval_bind(&mut cb, cl.kb, cn.kb, l, n, self.buses.bind, self.buses.acc, self.buses.mem, self.h.byte);
            groups.push((cl.kb.into(), cb.ints));
        }
        {
            let l: &GlueCols<AB::Var> = pl[..GLUE_W].borrow();
            let n: &GlueCols<AB::Var> = pn[..GLUE_W].borrow();
            let mut cb = Collect { inner: &mut *builder, ints: vec![] };
            eval_glue(&mut cb, l, n, cl.kg.into(), cn.kg.into(), &self.h);
            groups.push((cl.kg.into(), cb.ints));
        }
        {
            let l: &Hash2Cols<AB::Var> = pl[..HASH2_WIDTH].borrow();
            let n: &Hash2Cols<AB::Var> = pn[..HASH2_WIDTH].borrow();
            let mut cb = Collect { inner: &mut *builder, ints: vec![] };
            eval_hash(&mut cb, l, n, cl.kh.into(), cn.kh.into(), &self.h, &self.t);
            groups.push((cl.kh.into(), cb.ints));
        }
        {
            let l: &Samp2Cols<AB::Var> = pl[..SAMP2_WIDTH].borrow();
            let n: &Samp2Cols<AB::Var> = pn[..SAMP2_WIDTH].borrow();
            let mut cb = Collect { inner: &mut *builder, ints: vec![] };
            eval_samp(&mut cb, l, n, cl.ks.into(), cn.ks.into(), &self.h, &self.t);
            groups.push((cl.ks.into(), cb.ints));
        }
        merge_push(builder, groups);
    }
}

/// ALU and BIND roles.
fn eval_alu<AB: AirBuilderWithPublicValues + InteractionBuilder>(
    builder: &mut AB,
    cl: &NvCommon<AB::Var>,
    l: &AbCols<AB::Var>,
    n: &AbCols<AB::Var>,
    buses: &UBuses,
    byte_bus: BusIndex,
) where
    <AB::Expr as PrimeCharacteristicRing>::PrimeSubfield:
        p3_field::extension::BinomiallyExtendable<12>,
{
    let one = AB::Expr::ONE;
    let cst = |v: u64| AB::Expr::from_u64(v);
    let ka: AB::Expr = cl.ka.into();
    let p = cl.p;

    // ---------------- op selectors ----------------
    // g one-hot on ALU rows, zero elsewhere; h one-hot on ALU rows (free elsewhere)
    let mut gs = AB::Expr::ZERO;
    for &g in &l.g {
        builder.assert_zero(ka.clone() * g * (g - one.clone()));
        gs += g.into();
    }
    builder.assert_zero(ka.clone() * (gs - one.clone()));
    let mut hs = AB::Expr::ZERO;
    for &h in &l.h {
        builder.assert_zero(ka.clone() * h * (h - one.clone()));
        hs += h.into();
    }
    builder.assert_zero(ka.clone() * (hs - one.clone()));
    let s = |op: Op| -> AB::Expr {
        let v = op as usize;
        ka.clone() * l.h[v % OP_LO] * l.g[v / OP_LO]
    };
    let mut opv = AB::Expr::ZERO;
    for op in Op::all().into_iter().skip(1) {
        opv += s(op) * cst(op as u64);
    }
    let bfield = p[1] - opv * cst(1 << ADDR_BITS);

    // ---------------- ALU role ----------------
    let a: [AB::Expr; 12] = l.a.map(Into::into);
    let bb: [AB::Expr; 12] = l.b.map(Into::into);
    let ab = ext_field_multiply::<AB::Expr>(a.clone(), bb.clone());
    // Horn2 (two steps): (a b + w1) b + w2
    let h3: [AB::Expr; 12] = {
        let w1: AB::Expr = l.wit.into();
        let w2: AB::Expr = l.wit2.into();
        let mut t = ab.clone();
        t[0] += w1;
        let mut t = ext_field_multiply::<AB::Expr>(t, bb.clone());
        t[0] += w2;
        t
    };
    let free = s(Op::Load) + s(Op::Smp1) + s(Op::Smp12) + s(Op::Acc) + s(Op::Dig) + s(Op::PowChk) + s(Op::LoadBit) + s(Op::LoadF) + s(Op::SibWS4) + s(Op::SibWS2) + s(Op::DigWS4) + s(Op::DigWS2) + s(Op::HornR) + s(Op::HornE);
    let copy_a = s(Op::Unit1) + s(Op::UnitW) + s(Op::UnitWT) + s(Op::Unit12) + s(Op::Bit) + s(Op::Pv) + s(Op::PvD) + s(Op::UnitWS4) + s(Op::UnitWS2) + s(Op::HornS);
    // Horner chain: HornS sets the next row's c to its a; HornR sets the next row's c to
    // c * b + a (its own c was set by the previous row); the chain ends in HornE (free c)
    {
        let lc: [AB::Expr; 12] = core::array::from_fn(|k| l.c[k].into());
        let cb_ = ext_field_multiply::<AB::Expr>(lc, bb.clone());
        let mut tr = builder.when_transition();
        for k in 0..12 {
            tr.assert_zero(s(Op::HornS) * (n.c[k] - a[k].clone()));
            tr.assert_zero(s(Op::HornR) * (n.c[k] - cb_[k].clone() - a[k].clone()));
        }
    }
    let mulab = s(Op::Mul) + s(Op::Horn);
    for k in 0..12 {
        let mut e = mulab.clone() * ab[k].clone()
            + s(Op::Add) * (a[k].clone() + bb[k].clone())
            + s(Op::Sub) * (a[k].clone() - bb[k].clone())
            + s(Op::DblAdd) * (a[k].clone().double() + bb[k].clone())
            + s(Op::MulAddA) * (ab[k].clone() + a[k].clone())
            + copy_a.clone() * a[k].clone()
            + s(Op::Horn2) * h3[k].clone();
        if k == 0 {
            e += s(Op::Const) * p[0] + s(Op::Horn) * l.wit;
        }
        if k == 1 {
            e += s(Op::ConstX) * p[0];
        }
        builder.assert_zero((ka.clone() - free.clone()) * (l.c[k] - e));
        builder.assert_zero(s(Op::Zero) * l.a[k]);
        if k > 0 {
            builder.assert_zero(s(Op::Bit) * l.a[k]);
            builder.assert_zero(s(Op::Smp1) * l.c[k]);
        }
    }
    builder.assert_zero(s(Op::Bit) * l.a[0] * (l.a[0] - one.clone()));
    builder.assert_zero(s(Op::LoadBit) * l.c[0] * (l.c[0] - one.clone()));
    for k in 1..12 {
        builder.assert_zero((s(Op::LoadBit) + s(Op::LoadF)) * l.c[k]);
    }
    let pvs: Vec<AB::Expr> = builder.public_values().iter().map(|&x| x.into()).collect();
    builder.assert_zero(s(Op::Pv) * (l.a[0] - pvs[0].clone()));
    // statement digest (G1): PvD lo (P2 = 0) = public values 1..13, hi (P2 = 1) = 13..19
    builder.assert_zero(s(Op::PvD) * p[2] * (p[2] - one.clone()));
    for k in 0..12 {
        let hi = if k < 6 { pvs[13 + k].clone() } else { AB::Expr::ZERO };
        builder.assert_zero(s(Op::PvD) * (l.a[k] - (one.clone() - p[2]) * pvs[1 + k].clone() - p[2] * hi));
    }


    // memory: ALU rows offer (y, c); operand reads on ALU rows, E1/E2 reads on BIND rows
    let mem = LookupBus::new(buses.mem);
    let key = |addr: AB::Expr, v: &[AB::Var; 12]| -> Vec<AB::Expr> {
        core::iter::once(addr).chain(v.iter().map(|&t| t.into())).collect()
    };
    mem.add_key_with_lookups(builder, key(cl.y.into(), &l.c), ka.clone() * l.mult);
    let sum_of = |f: fn(Op) -> bool| -> AB::Expr {
        Op::all()
            .into_iter()
            .filter(|&o| f(o))
            .map(|o| s(o))
            .fold(AB::Expr::ZERO, |x, t| x + t)
    };
    let reads_a = sum_of(Op::reads_a);
    let reads_b = sum_of(Op::reads_b);
    mem.lookup_key(builder, key(p[0].into(), &l.a), reads_a);
    mem.lookup_key(builder, key(bfield.clone(), &l.b), reads_b);

    // slot bus (chan, key1, key2, kind, v0, v1, v2):
    //   units (chan 1, job P2, uidx, kind 0 felt | 2 word, value(s)) are sent;
    //   samples (chan 0, tidx P2 + k, 0, KIND_SAMPLE, c_k) are received;
    //   transcript anchors (chan 2, job P2, 0, 0, A, B, 0) are sent.
    let slot = PermutationCheckBus::new(buses.slot);
    let smp = s(Op::Smp1) + s(Op::Smp12);
    // UnitWS*: units of the a operand at P3 + 2k + 12 bit; DigWS*: the same from a child digest
    let ws = s(Op::UnitWS4) + s(Op::UnitWS2) + s(Op::DigWS4) + s(Op::DigWS2);
    // Merkle sibling ops: free c, units at P3 + 2k + 12 (1 - bit)
    let sib = s(Op::SibWS4) + s(Op::SibWS2);
    for k in 6..12 {
        builder.assert_zero((s(Op::SibWS2) + s(Op::DigWS2)) * l.c[k]);
    }
    let wt = s(Op::UnitWT);
    let chan = s(Op::Unit1) + s(Op::UnitW) + wt.clone() + ws.clone() + sib.clone() + s(Op::Unit12) + s(Op::Horn) + s(Op::Horn2) + s(Op::Job) + s(Op::Anchor).double()
        + s(Op::PowChk) * cst(3);
    for k in 0..12usize {
        let kk = cst(k as u64);
        let mut v_h3 = AB::Expr::ZERO;
        let mut send = s(Op::Unit12);
        let mut recv = s(Op::Smp12);
        if k < 2 {
            send += s(Op::Horn2);
        }
        if k == 0 {
            send += s(Op::Unit1) + s(Op::Horn) + s(Op::Job) + s(Op::Anchor);
            recv += s(Op::Smp1) + s(Op::PowChk);
        }
        if k == 1 {
            send += s(Op::Job);
        }
        if k < 2 {
            send += s(Op::UnitW) + ws.clone() + sib.clone() + wt.clone();
        } else if k < 4 {
            send += s(Op::UnitWS4) + s(Op::SibWS4) + s(Op::DigWS4);
            // B in {2, 4}: words 2, 3 only for B = 4
            send += s(Op::UnitW) * (bfield.clone() - cst(2)) * cst(p3_field::PrimeField32::as_canonical_u32(&F::TWO.inverse()) as u64);
        }
        let key1 = p[2] + s(Op::Smp12) * kk.clone();
        let mut key2 = s(Op::Unit12) * (p[3] + kk.clone())
            + (s(Op::UnitW) + wt.clone()) * (p[3] + cst(2 * k as u64))
            + ws.clone() * (p[3] + cst(2 * k as u64) + l.b[0] * cst(12))
            + sib.clone() * (p[3] + cst(2 * k as u64 + 12) - l.b[0] * cst(12))
            + s(Op::Job) * kk.clone();
        if k == 0 {
            key2 += (s(Op::Horn) + s(Op::Unit1)) * p[3];
        }
        if k < 2 {
            key2 += s(Op::Horn2) * (p[3] + kk.clone());
            let w: AB::Expr = [l.wit2, l.wit][k].into();
            v_h3 = s(Op::Horn2) * w;
        }
        let mut kind = (s(Op::UnitW) + ws.clone() + sib.clone()).double() + smp.clone() * cst(KIND_SAMPLE as u64);
        if k < 2 {
            // UnitWT: word unit (kind 2), then the 42-B digest tail (kind UNIT_HALF)
            let kk = if k == 0 { super::hash::UNIT_WORD } else { super::hash::UNIT_HALF };
            kind += wt.clone() * cst(kk as u64);
        }
        let mut v = [AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ZERO];
        v[0] = (s(Op::Unit12) + s(Op::Smp12)) * l.c[k] + v_h3.clone();
        if k == 0 {
            for t in 0..3 {
                v[t] += s(Op::PowChk) * l.c[t];
            }
            v[0] += (s(Op::Unit1) + s(Op::Smp1)) * l.c[0]
                + s(Op::Horn) * l.wit
                + s(Op::Job) * bfield.clone()
                + s(Op::Anchor) * p[0];
            v[1] += s(Op::Anchor) * bfield.clone();
            // anchor k2: the hash tag in the low bits (binds the job's op: flush / commit /
            // PoW) plus the chain-start flag at ANCHOR_FIRST_BIT
            v[2] += s(Op::Anchor) * p[3];
        }
        if k < 4 {
            for t in 0..3 {
                v[t] += (s(Op::UnitW) + ws.clone() + sib.clone() + if k < 2 { wt.clone() } else { AB::Expr::ZERO }) * l.c[3 * k + t];
            }
        }
        let [v0, v1, v2] = v;
        slot.send(builder, [chan.clone(), key1, key2, kind, v0, v1, v2], send - recv);
    }
    // job starts (leaf / node jobs): (job P2, tag P0).  A Merkle path level's node job is
    // started by its SibWS4 row (P0 = NODE_TAG in the program; SibWS4 reads no a operand), so the
    // level needs no separate NodeJob row.
    PermutationCheckBus::new(buses.job).send(builder, [p[2].into(), p[0].into(), AB::Expr::ONE], s(Op::Job) + s(Op::NodeJob) + s(Op::SibWS4));
    // digests: pairs P3, P3 + 1 (if B = 2) of job P2
    let dig = PermutationCheckBus::new(buses.digest);
    // Dig: job P2, pairs P3, P3 + 1 (B = 2) or P3 (B = 1); DigWS4: job P0, pairs 0, 1;
    // DigWS2: job P0, pair 2
    let (dws4, dws2) = (s(Op::DigWS4), s(Op::DigWS2));
    for h in 0..2usize {
        let job = s(Op::Dig) * p[2] + (dws4.clone() + dws2.clone()) * p[0];
        let pair = s(Op::Dig) * (p[3] + cst(h as u64)) + dws4.clone() * cst(h as u64) + dws2.clone() * cst(2);
        let mut m = vec![job, pair];
        m.extend((0..6).map(|t| l.c[6 * h + t].into()));
        let mult = if h == 0 {
            s(Op::Dig) + dws4.clone() + dws2.clone()
        } else {
            s(Op::Dig) * (bfield.clone() - one.clone()) + dws4.clone()
        };
        dig.receive(builder, m, mult);
    }
    for k in 6..12 {
        builder.assert_zero(s(Op::Dig) * (cst(2) - bfield.clone()) * l.c[k]);
    }

    // B field range: B = rx + 256 ry + 65536 rz in [0, 2^24) binds the op to P1 (every ALU row;
    // the app-table data rows, the one exemption, are gone with G2)
    let nd = ka.clone();
    builder.assert_zero(nd.clone() * (bfield.clone() - l.rx - l.ry * cst(256) - l.rz * cst(65536)));
    super::hash::lookup_pair(builder, byte_bus, l.rx, l.ry, nd.clone());
    // rz a byte (24-bit B field): the pair (rz, 0) is in the byte-pair table.  (With the old
    // 20-bit field rz < 16 was the pair (rz, 16 rz); a lone lookup of 16 rz only gave
    // rz = t / 16 mod p for a byte t, which allowed op -> op - 1.)
    // relabels such as Zero -> Bit; see FAITHFUL.md, bug B1.)
    super::hash::lookup_pair(builder, byte_bus, l.rz, AB::Expr::ZERO, nd);
    // ALU rows send (y, P) to the BIND rows; the binding total arrives at the `Acc` row
    let mut bmsg: Vec<AB::Expr> = vec![cl.y.into()];
    bmsg.extend(p.iter().map(|&x| x.into()));
    PermutationCheckBus::new(buses.bind).send(builder, bmsg, ka.clone());
    // `Acc` row: P0 = last BIND pair index (= prog_len - 2), pinning the BIND region
    let mut amsg: Vec<AB::Expr> = l.c.iter().map(|&x| x.into()).collect();
    amsg.push(p[0].into());
    PermutationCheckBus::new(buses.acc).receive(builder, amsg, s(Op::Acc));
}

/// BIND role: row t covers ALU rows y = 2t, 2t + 1 (y = ya + 512 yb, ya even).
fn eval_bind<AB: AirBuilder + InteractionBuilder>(
    builder: &mut AB,
    kl: AB::Var,
    kn: AB::Var,
    l: &BindCols<AB::Var>,
    n: &BindCols<AB::Var>,
    bind_bus: BusIndex,
    acc_bus: BusIndex,
    mem_bus: BusIndex,
    byte_bus: BusIndex,
) where
    <AB::Expr as PrimeCharacteristicRing>::PrimeSubfield:
        p3_field::extension::BinomiallyExtendable<12>,
{
    let one = AB::Expr::ONE;
    let cst = |v: u64| AB::Expr::from_u64(v);
    let kb: AB::Expr = kl.into();
    let tp = tau_pows();
    let ptau = |pc: &[AB::Var; 4]| -> [AB::Expr; 12] {
        let mut acc: [AB::Expr; 12] = core::array::from_fn(|_| AB::Expr::ZERO);
        for j in 0..4 {
            let cf: &[F] = tp[j].as_basis_coefficients_slice();
            for k in 0..12 {
                acc[k] += pc[j] * AB::Expr::from_u32(p3_field::PrimeField32::as_canonical_u32(&cf[k]));
            }
        }
        acc
    };
    let e1a: [AB::Expr; 12] = l.e1a.map(Into::into);
    let e1b: [AB::Expr; 12] = l.e1b.map(Into::into);
    let e2: [AB::Expr; 12] = l.e2.map(Into::into);
    let inner = ext_field_add::<AB::Expr>(
        ext_field_multiply::<AB::Expr>(e1a, ptau(&l.pc0)),
        ext_field_multiply::<AB::Expr>(e1b, ptau(&l.pc1)),
    );
    let wp = ext_field_multiply::<AB::Expr>(e2, inner);
    let y2 = |x: &BindCols<AB::Var>| x.ya + x.yb * cst(E1_SIZE as u64);
    builder.assert_zero(kb.clone() * l.bl * (l.bl - one.clone()));
    builder.when_last_row().assert_zero(kb.clone() * (one.clone() - l.bl));
    {
        let mut t = builder.when_transition();
        let entry = kn * (one.clone() - kl);
        t.assert_zero(entry.clone() * y2(n));
        for k in 0..12 {
            t.assert_zero(entry.clone() * n.acc[k]);
        }
        t.assert_zero(kl * (l.bl - (one.clone() - kn)));
        let both = kl * kn;
        t.assert_zero(both.clone() * (y2(n) - y2(l) - cst(2)));
        for k in 0..12 {
            t.assert_zero(both.clone() * (n.acc[k] - l.acc[k] - wp[k].clone()));
        }
    }
    // ya even in [0, 510]: ya / 2 is a byte
    let inv2 = p3_field::PrimeField32::as_canonical_u32(&F::TWO.inverse()) as u64;
    super::hash::lookup_byte(builder, byte_bus, l.ya * cst(inv2), kb.clone());
    let mem = LookupBus::new(mem_bus);
    let key = |addr: AB::Expr, v: &[AB::Var; 12]| -> Vec<AB::Expr> {
        core::iter::once(addr).chain(v.iter().map(|&t| t.into())).collect()
    };
    mem.lookup_key(builder, key(l.ya.into(), &l.e1a), kb.clone());
    mem.lookup_key(builder, key(l.ya + one.clone(), &l.e1b), kb.clone());
    mem.lookup_key(builder, key(l.yb + cst(E1_SIZE as u64), &l.e2), kb.clone());
    let bind = PermutationCheckBus::new(bind_bus);
    for (h, pc) in [&l.pc0, &l.pc1].into_iter().enumerate() {
        let mut m = vec![y2(l) + cst(h as u64)];
        m.extend(pc.iter().map(|&x| x.into()));
        bind.receive(builder, m, kb.clone());
    }
    // total and the last row's pair index (pins the BIND region length)
    let mut amsg: Vec<AB::Expr> = (0..12).map(|k| l.acc[k] + wp[k].clone()).collect();
    amsg.push(y2(l));
    PermutationCheckBus::new(acc_bus).send(builder, amsg, kb * l.bl);
}

/// NvAir trace: ALU rows (program, length 2^prog_log), BIND rows, GLUE / HASH / SAMP rows,
/// padding to 2^log_h.  E1 / E2 are read from `vals[ya]`, `vals[512 + yb]`.
pub fn nv_trace(
    instrs: &[Instr],
    vals: &[EF],
    wits: &[F],
    wits_x: &std::collections::BTreeMap<usize, F>,
    glue: &[[F; GLUE_W]],
    hash: &[[F; HASH2_WIDTH]],
    samp: &[[F; SAMP2_WIDTH]],
    log_h: usize,
    counts: &mut [u32],
) -> RowMajorMatrix<F> {
    let na = instrs.len();
    assert!(na % 2 == 0 && na >= E1_SIZE);
    let used = na + na / 2 + glue.len() + hash.len() + samp.len();
    assert!(used <= 1 << log_h, "NvAir: {used} rows exceed 2^{log_h}");
    let h = 1usize << log_h;
    let w = NV_WIDTH;
    let mut reads = vec![0u32; na];
    for ins in instrs {
        if ins.op.reads_a() {
            reads[ins.a as usize] += 1;
        }
        if ins.op.reads_b() {
            reads[ins.b as usize] += 1;
        }
    }
    for t in 0..na / 2 {
        let y = 2 * t;
        reads[y % E1_SIZE] += 1;
        reads[y % E1_SIZE + 1] += 1;
        reads[E1_SIZE + y / E1_SIZE] += 1;
        super::hash::cnt2(counts, (y % E1_SIZE) / 2, 0);
    }
    let coeffs = |x: EF| -> [F; 12] { x.as_basis_coefficients_slice().try_into().unwrap() };
    let mut t = F::zero_vec(h * w);
    for (y, ins) in instrs.iter().enumerate() {
        let row = &mut t[y * w..(y + 1) * w];
        let (cm, pool) = row.split_at_mut(N_COMMON);
        let c: &mut NvCommon<F> = cm.borrow_mut();
        c.ka = F::ONE;
        c.p = ins.words().map(F::from_u32);
        let r: &mut AbCols<F> = pool[..AB_W].borrow_mut();
        if ins.op.reads_a() {
            r.a = coeffs(vals[ins.a as usize]);
        }
        if ins.op.reads_b() {
            r.b = coeffs(vals[ins.b as usize]);
        }
        r.c = coeffs(vals[y]);
        let v = ins.op as usize;
        r.h[v % OP_LO] = F::ONE;
        r.g[v / OP_LO] = F::ONE;
        r.wit = wits[y];
        if let Some(&w2) = wits_x.get(&y) {
            r.wit2 = w2;
        }
        r.mult = F::from_u32(reads[y]);
        let bf = ins.b as usize;
        assert!(bf < 1 << super::isa::ADDR_BITS);
        r.rx = F::from_usize(bf & 255);
        r.ry = F::from_usize((bf >> 8) & 255);
        r.rz = F::from_usize(bf >> 16);
        super::hash::cnt2(counts, bf & 255, (bf >> 8) & 255);
        super::hash::cnt2(counts, bf >> 16, 0);
    }
    let tp = tau_pows();
    let mut acc = EF::ZERO;
    let nb = na / 2;
    for bt in 0..nb {
        let y = 2 * bt;
        let row = &mut t[(na + bt) * w..(na + bt + 1) * w];
        let (cm, pool) = row.split_at_mut(N_COMMON);
        let c: &mut NvCommon<F> = cm.borrow_mut();
        c.kb = F::ONE;
        let r: &mut BindCols<F> = pool[..BIND_W].borrow_mut();
        let (ya, yb) = (y % E1_SIZE, y / E1_SIZE);
        let (e1a, e1b, e2) = (vals[ya], vals[ya + 1], vals[E1_SIZE + yb]);
        r.e1a = coeffs(e1a);
        r.e1b = coeffs(e1b);
        r.e2 = coeffs(e2);
        r.acc = coeffs(acc);
        let (w0, w1) = (instrs[y].words(), instrs[y + 1].words());
        for j in 0..4 {
            r.pc0[j] = F::from_u32(w0[j]);
            r.pc1[j] = F::from_u32(w1[j]);
        }
        r.ya = F::from_usize(ya);
        r.yb = F::from_usize(yb);
        r.bl = F::from_bool(bt + 1 == nb);
        let pw = |wd: [u32; 4]| -> EF { (0..4).map(|j| tp[j] * F::from_u32(wd[j])).sum() };
        acc += e2 * (e1a * pw(w0) + e1b * pw(w1));
    }
    debug_assert!(vals.contains(&acc), "ACC row must hold the full binding sum");
    let mut row = na + na / 2;
    let mut put = |flag: usize, data: &[F]| {
        let r = &mut t[row * w..(row + 1) * w];
        r[flag] = F::ONE;
        r[N_COMMON..N_COMMON + data.len()].copy_from_slice(data);
        row += 1;
    };
    for g in glue {
        put(core::mem::offset_of!(NvCommon<u8>, kg), g);
    }
    for x in hash {
        put(core::mem::offset_of!(NvCommon<u8>, kh), x);
    }
    for x in samp {
        put(core::mem::offset_of!(NvCommon<u8>, ks), x);
    }
    for r in 0..used {
        t[r * w + core::mem::offset_of!(NvCommon<u8>, y)] = F::from_usize(r);
    }
    RowMajorMatrix::new(t, w)
}

#[allow(dead_code)]
fn _w(m: &RowMajorMatrix<F>) -> usize {
    m.width()
}
