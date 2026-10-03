//! Fast batch evaluation of a constraint [`Tape`] combined with powers of
//! `α` — the prover's quotient hot loop.
//!
//! [`BlockEval::new`] compiles a tape into a register program over packed
//! base-field values (`<F as Field>::Packing`, 8 lanes on AVX2, 16 on
//! AVX-512, 1 without SIMD), each register holding `U` packed vectors, i.e.
//! `L = WIDTH·U` consecutive rows:
//!
//! * public inputs and constants are folded (`x + 0`, `x·1`, `x·0`,
//!   `x·(−1)`, `−(−x)`, `x − x`, constant arithmetic), the result is
//!   hash-consed again and dead code is removed;
//! * `x + (−y)` becomes a single `Sub`;
//! * column reads disappear: the used columns of the current and of the next
//!   row are transposed into dedicated registers once per row group, and the
//!   selectors / constants live in fixed registers, so every instruction is
//!   a 3-address packed `Add`/`Sub`/`Mul`/`Neg`;
//! * temporaries get registers by linear-scan over their live ranges (the
//!   register file stays a few KiB, L1-resident);
//! * outputs of the form `sel · e` (`sel` ∈ {isFirst, isLast, isTransition})
//!   are accumulated into a per-selector group and multiplied by the
//!   selector once per row at the end; outputs that coincide after
//!   hash-consing are merged (their `α^k` are summed per call);
//! * the combination `Σ_k α^k · c_k` is computed as 8 base-field dot products
//!   (one per limb of `K = F[X]/(X^8 − 11)`) with *delayed reduction*: the
//!   canonical limb of the coefficient times the Montgomery word of `c_k` is
//!   accumulated in a `u64` lane (`Σ a·(vR) ≡ R·Σ a v`, so the reduced sum is
//!   directly the Montgomery word of the result), with a cheap 32-bit fold
//!   every 4 terms and one `% p` per limb per row at the end.

use std::collections::HashMap;

use p3_field::{BasedVectorSpace, Field, PackedValue, PrimeCharacteristicRing, PrimeField32};

use crate::air::{Op, Tape};
use crate::field::{EF, F, P};

/// Packed base field.
pub type PF = <F as Field>::Packing;
/// SIMD width of [`PF`].
pub const W: usize = <PF as PackedValue>::WIDTH;
/// Packed vectors per register (rows per group = `W · U`).
const U: usize = if W >= 16 { 1 } else if W >= 8 { 2 } else { 8 };
const L: usize = W * U;

/// Selector groups: 0 = plain, 1 = isFirst, 2 = isLast, 3 = isTransition.
const NGROUPS: usize = 4;
/// Terms that may be added to a folded `u64` accumulator before the next fold.
/// After a fold the value is `< 2^32 + 2^32·(2^32 − 2p) < 2^60.01`; each term
/// is `< p^2 < 2^61.82`, and `2^60.01 + 4·(p−1)^2 < 2^64`.
const TERMS_PER_FOLD: u32 = 4;
/// `2^32 mod p`.
const R32: u64 = (1u64 << 32) % (P as u64);

/// A value in the compiled program before register allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum V {
    /// canonical constant
    K(u32),
    Cur(u32),
    Nxt(u32),
    /// 0 = isFirst, 1 = isLast, 2 = isTransition
    Sel(u8),
    /// node index
    N(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum NOp {
    Add(V, V),
    Sub(V, V),
    Mul(V, V),
    Neg(V),
}

/// Register-machine instruction. Registers are `u32` indices into the
/// register file; `k` indexes the constant table.
#[derive(Clone, Copy, Debug)]
enum Ins {
    Add(u32, u32, u32),
    Sub(u32, u32, u32),
    Mul(u32, u32, u32),
    Neg(u32, u32),
    /// `d = a + k`
    AddK(u32, u32, u32),
    /// `d = k − a`
    KSub(u32, u32, u32),
    /// `d = a · k`
    MulK(u32, u32, u32),
    /// `d = k`
    Const(u32, u32),
    /// `d = column c of the current rows`
    LoadCur(u32, u32),
    /// `d = column c of the next rows`
    LoadNxt(u32, u32),
    /// accumulate register `src` into group `g` with merged coefficient `coef`
    Acc { g: u32, src: u32, coef: u32 },
    /// fold the `u64` accumulators of group `g`
    Fold(u32),
}

/// Compiled tape (see the module docs).
#[derive(Clone, Debug)]
pub struct BlockEval {
    prog: Vec<Ins>,
    nregs: usize,
    consts: Vec<F>,
    /// register of each selector, if used
    sel: [Option<u32>; 3],
    /// largest column index read (+1), 0 if none
    max_col: usize,
    /// constraint indices whose `α^k` sum to merged coefficient `i`
    coef_terms: Vec<Vec<u32>>,
    /// which groups are non-empty
    groups_used: [bool; NGROUPS],
    num_constraints: usize,
}

struct Builder {
    nodes: Vec<NOp>,
    memo: HashMap<NOp, u32>,
}

const ZERO: V = V::K(0);
const ONE: V = V::K(1);
const MINUS_ONE: V = V::K(P - 1);

fn kf(c: u32) -> F {
    F::new(c)
}
fn fk(x: F) -> V {
    V::K(x.as_canonical_u32())
}

impl Builder {
    fn node(&mut self, op: NOp) -> V {
        if let Some(&i) = self.memo.get(&op) {
            return V::N(i);
        }
        self.nodes.push(op);
        let i = (self.nodes.len() - 1) as u32;
        self.memo.insert(op, i);
        V::N(i)
    }
    fn neg_of(&self, v: V) -> Option<V> {
        match v {
            V::N(i) => match self.nodes[i as usize] {
                NOp::Neg(x) => Some(x),
                _ => None,
            },
            _ => None,
        }
    }
    fn add(&mut self, a: V, b: V) -> V {
        match (a, b) {
            (V::K(x), V::K(y)) => fk(kf(x) + kf(y)),
            (ZERO, y) | (y, ZERO) => y,
            _ => {
                if let Some(y) = self.neg_of(b) {
                    return self.sub(a, y);
                }
                if let Some(x) = self.neg_of(a) {
                    return self.sub(b, x);
                }
                let (a, b) = if a <= b { (a, b) } else { (b, a) };
                self.node(NOp::Add(a, b))
            }
        }
    }
    fn sub(&mut self, a: V, b: V) -> V {
        match (a, b) {
            (V::K(x), V::K(y)) => fk(kf(x) - kf(y)),
            (x, ZERO) => x,
            (ZERO, y) => self.neg(y),
            _ if a == b => ZERO,
            _ => {
                if let Some(y) = self.neg_of(b) {
                    return self.add(a, y);
                }
                self.node(NOp::Sub(a, b))
            }
        }
    }
    fn mul(&mut self, a: V, b: V) -> V {
        match (a, b) {
            (V::K(x), V::K(y)) => fk(kf(x) * kf(y)),
            (ZERO, _) | (_, ZERO) => ZERO,
            (ONE, y) | (y, ONE) => y,
            (MINUS_ONE, y) | (y, MINUS_ONE) => self.neg(y),
            _ => {
                let (a, b) = if a <= b { (a, b) } else { (b, a) };
                self.node(NOp::Mul(a, b))
            }
        }
    }
    fn neg(&mut self, a: V) -> V {
        if let V::K(x) = a {
            return fk(-kf(x));
        }
        if let Some(x) = self.neg_of(a) {
            return x;
        }
        if let V::N(i) = a {
            if let NOp::Sub(x, y) = self.nodes[i as usize] {
                return self.sub(y, x);
            }
        }
        self.node(NOp::Neg(a))
    }
}

impl BlockEval {
    /// Compile `tape` for public inputs `pubs`.
    pub fn new(tape: &Tape, pubs: &[F]) -> Self {
        let mut b = Builder { nodes: vec![], memo: HashMap::new() };
        let mut vals: Vec<V> = Vec::with_capacity(tape.ops.len());
        for op in &tape.ops {
            let v = match *op {
                Op::Const(c) => fk(F::new(c)),
                Op::Col(c, false) => V::Cur(c),
                Op::Col(c, true) => V::Nxt(c),
                Op::Pub(i) => fk(pubs[i as usize]),
                Op::IsFirst => V::Sel(0),
                Op::IsLast => V::Sel(1),
                Op::IsTransition => V::Sel(2),
                Op::Add(x, y) => b.add(vals[x as usize], vals[y as usize]),
                Op::Mul(x, y) => b.mul(vals[x as usize], vals[y as usize]),
                Op::Neg(x) => b.neg(vals[x as usize]),
            };
            vals.push(v);
        }

        // Outputs: split off a selector factor, merge equal (group, value).
        let mut acc_of: HashMap<(u8, V), u32> = HashMap::new();
        let mut accs: Vec<(u8, V)> = vec![];
        let mut coef_terms: Vec<Vec<u32>> = vec![];
        for (k, &o) in tape.outputs.iter().enumerate() {
            let v = vals[o as usize];
            let (g, x) = match v {
                ZERO => continue,
                V::Sel(s) => (s + 1, ONE),
                V::N(i) => match b.nodes[i as usize] {
                    NOp::Mul(V::Sel(s), x) | NOp::Mul(x, V::Sel(s)) => (s + 1, x),
                    _ => (0, v),
                },
                _ => (0, v),
            };
            if x == ZERO {
                continue;
            }
            let id = *acc_of.entry((g, x)).or_insert_with(|| {
                accs.push((g, x));
                coef_terms.push(vec![]);
                (accs.len() - 1) as u32
            });
            coef_terms[id as usize].push(k as u32);
        }

        // Liveness of nodes (nodes are in topological order).
        let nn = b.nodes.len();
        let mut live = vec![false; nn];
        for &(_, x) in &accs {
            if let V::N(i) = x {
                live[i as usize] = true;
            }
        }
        for i in (0..nn).rev() {
            if live[i] {
                for v in operands(&b.nodes[i]) {
                    if let V::N(j) = v {
                        live[j as usize] = true;
                    }
                }
            }
        }

        // Schedule: each live node in order, followed by its accumulations;
        // accumulations of leaves first.
        #[derive(Clone, Copy)]
        enum S {
            Node(u32),
            Acc(u32),
        }
        let mut accs_of_node: Vec<Vec<u32>> = vec![vec![]; nn];
        let mut sched: Vec<S> = vec![];
        for (id, &(_, x)) in accs.iter().enumerate() {
            match x {
                V::N(i) => accs_of_node[i as usize].push(id as u32),
                _ => sched.push(S::Acc(id as u32)),
            }
        }
        for i in 0..nn {
            if live[i] {
                sched.push(S::Node(i as u32));
                sched.extend(accs_of_node[i].iter().map(|&a| S::Acc(a)));
            }
        }
        let uses = |s: S| -> Vec<V> {
            match s {
                S::Node(i) => operands(&b.nodes[i as usize]),
                S::Acc(a) => vec![accs[a as usize].1],
            }
        };

        // Last use of every register-resident value.
        let mut last: HashMap<V, usize> = HashMap::new();
        for (t, &s) in sched.iter().enumerate() {
            for v in uses(s) {
                last.insert(v, t);
            }
        }

        // Selectors live in fixed registers; everything else is allocated by
        // linear scan (columns are loaded right before their first use).
        let mut nregs = 0u32;
        let mut sel = [None; 3];
        for s in 0..3u8 {
            if last.contains_key(&V::Sel(s)) {
                sel[s as usize] = Some(nregs);
                nregs += 1;
            }
        }
        let mut consts: Vec<F> = vec![];
        let mut const_idx: HashMap<u32, u32> = HashMap::new();
        let mut kidx = |c: u32| -> u32 {
            *const_idx.entry(c).or_insert_with(|| {
                consts.push(F::new(c));
                (consts.len() - 1) as u32
            })
        };
        let mut max_col = 0usize;
        let mut free: Vec<u32> = vec![];
        let mut reg: HashMap<V, u32> = HashMap::new();
        for s in 0..3u8 {
            if let Some(r) = sel[s as usize] {
                reg.insert(V::Sel(s), r);
            }
        }
        let mut alloc = |free: &mut Vec<u32>| {
            free.pop().unwrap_or_else(|| {
                nregs += 1;
                nregs - 1
            })
        };
        let mut prog: Vec<Ins> = Vec::with_capacity(sched.len() * 2);
        let mut pending = [0u32; NGROUPS];
        let mut groups_used = [false; NGROUPS];
        for (t, &s) in sched.iter().enumerate() {
            let ops = uses(s);
            // materialize leaves
            for &v in &ops {
                if reg.contains_key(&v) {
                    continue;
                }
                let ins = match v {
                    V::Cur(c) => {
                        max_col = max_col.max(c as usize + 1);
                        Ins::LoadCur(0, c)
                    }
                    V::Nxt(c) => {
                        max_col = max_col.max(c as usize + 1);
                        Ins::LoadNxt(0, c)
                    }
                    // constant operands of arithmetic are inlined
                    V::K(c) if matches!(s, S::Acc(_)) => Ins::Const(0, kidx(c)),
                    _ => continue,
                };
                let d = alloc(&mut free);
                prog.push(with_dst(ins, d));
                reg.insert(v, d);
            }
            let r = |v: &V| reg[v];
            match s {
                S::Node(i) => {
                    let op = b.nodes[i as usize];
                    let lowered = match op {
                        NOp::Add(V::K(k), a) | NOp::Add(a, V::K(k)) => Ins::AddK(0, r(&a), kidx(k)),
                        NOp::Sub(a, V::K(k)) => Ins::AddK(0, r(&a), kidx(P - k)),
                        NOp::Sub(V::K(k), a) => Ins::KSub(0, r(&a), kidx(k)),
                        NOp::Mul(V::K(k), a) | NOp::Mul(a, V::K(k)) => Ins::MulK(0, r(&a), kidx(k)),
                        NOp::Add(x, y) => Ins::Add(0, r(&x), r(&y)),
                        NOp::Sub(x, y) => Ins::Sub(0, r(&x), r(&y)),
                        NOp::Mul(x, y) => Ins::Mul(0, r(&x), r(&y)),
                        NOp::Neg(x) => Ins::Neg(0, r(&x)),
                    };
                    // operands dying here free their registers before the
                    // result is allocated (operands are read before the write)
                    release(&ops, t, &last, &mut reg, &mut free);
                    let d = alloc(&mut free);
                    prog.push(with_dst(lowered, d));
                    reg.insert(V::N(i), d);
                }
                S::Acc(a) => {
                    let (g, x) = accs[a as usize];
                    let g = g as usize;
                    groups_used[g] = true;
                    if pending[g] == TERMS_PER_FOLD {
                        prog.push(Ins::Fold(g as u32));
                        pending[g] = 0;
                    }
                    pending[g] += 1;
                    prog.push(Ins::Acc { g: g as u32, src: r(&x), coef: a });
                    release(&ops, t, &last, &mut reg, &mut free);
                }
            }
        }

        BlockEval {
            prog,
            nregs: nregs as usize,
            consts,
            sel,
            max_col,
            coef_terms,
            groups_used,
            num_constraints: tape.outputs.len(),
        }
    }

    /// Number of program instructions (for diagnostics).
    pub fn num_instructions(&self) -> usize {
        self.prog.len()
    }
    /// Number of packed registers (for diagnostics).
    pub fn num_registers(&self) -> usize {
        self.nregs
    }

    /// `out[i] = Σ_k alpha_pow[k] · C_k(row i)` for `i in 0..out.len()`,
    /// where row `i` of the table is `rows[i·width .. (i+1)·width]`, its
    /// "next" row is row `next[i]` of `rows`, `isFirst = sel_first[i]`,
    /// `isLast = sel_last[i]` and `isTransition = 1 − sel_last[i]`.
    #[allow(clippy::too_many_arguments)]
    pub fn eval_combined(
        &self,
        rows: &[F],
        width: usize,
        next: &[u32],
        sel_first: &[F],
        sel_last: &[F],
        alpha_pow: &[EF],
        out: &mut [EF],
    ) {
        let n = out.len();
        if n == 0 {
            return;
        }
        assert!(alpha_pow.len() >= self.num_constraints, "alpha_pow too short");
        assert!(next.len() >= n && sel_first.len() >= n && sel_last.len() >= n);
        assert!(self.max_col <= width, "column out of range");
        assert!(rows.len() >= n * width);
        let nrows = if width == 0 { usize::MAX } else { rows.len() / width };
        assert!(next[..n].iter().all(|&j| (j as usize) < nrows), "next row out of range");

        // merged coefficients, canonical limbs
        let coefs: Vec<[u64; 8]> = self
            .coef_terms
            .iter()
            .map(|ks| {
                let s: EF = ks.iter().map(|&k| alpha_pow[k as usize]).sum();
                let c: &[F] = s.as_basis_coefficients_slice();
                std::array::from_fn(|j| c[j].as_canonical_u32() as u64)
            })
            .collect();

        let mut regs: Vec<[PF; U]> = vec![[PF::ZERO; U]; self.nregs];
        let mut acc = vec![0u64; NGROUPS * 8 * L];
        let mut cur_off = [0usize; L];
        let mut nxt_off = [0usize; L];
        let mut i0 = 0;
        while i0 < n {
            let cnt = (n - i0).min(L);
            // Rows past `cnt` (tail group) repeat the last valid row; their
            // results are discarded.
            {
                let raw = raw_regs_mut(&mut regs);
                for l in 0..L {
                    let i = i0 + l.min(cnt - 1);
                    cur_off[l] = i * width;
                    nxt_off[l] = next[i] as usize * width;
                    if let Some(r) = self.sel[0] {
                        raw[r as usize * L + l] = sel_first[i];
                    }
                    if let Some(r) = self.sel[1] {
                        raw[r as usize * L + l] = sel_last[i];
                    }
                    if let Some(r) = self.sel[2] {
                        raw[r as usize * L + l] = F::ONE - sel_last[i];
                    }
                }
            }
            acc.iter_mut().for_each(|a| *a = 0);
            let ctx = Ctx { rows, cur_off: &cur_off, nxt_off: &nxt_off, consts: &self.consts, coefs: &coefs };
            run(&self.prog, &mut regs, &ctx, &mut acc);
            // finalize
            for l in 0..cnt {
                let i = i0 + l;
                let fsel = [F::ONE, sel_first[i], sel_last[i], F::ONE - sel_last[i]];
                let mut limbs = [F::ZERO; 8];
                for g in 0..NGROUPS {
                    if !self.groups_used[g] {
                        continue;
                    }
                    for (j, limb) in limbs.iter_mut().enumerate() {
                        let v = from_monty((acc[(g * 8 + j) * L + l] % P as u64) as u32);
                        *limb += if g == 0 { v } else { v * fsel[g] };
                    }
                }
                out[i] = EF::from_basis_coefficients_fn(|j| limbs[j]);
            }
            i0 += L;
        }
    }
}

fn operands(op: &NOp) -> Vec<V> {
    match *op {
        NOp::Add(x, y) | NOp::Sub(x, y) | NOp::Mul(x, y) => vec![x, y],
        NOp::Neg(x) => vec![x],
    }
}

/// Free the registers of operands whose last use is step `t` (selectors are
/// never freed).
fn release(ops: &[V], t: usize, last: &HashMap<V, usize>, reg: &mut HashMap<V, u32>, free: &mut Vec<u32>) {
    for v in ops {
        if matches!(v, V::Sel(_)) || last.get(v) != Some(&t) {
            continue;
        }
        if let Some(r) = reg.remove(v) {
            free.push(r);
        }
    }
}

fn with_dst(ins: Ins, d: u32) -> Ins {
    match ins {
        Ins::Add(_, a, b) => Ins::Add(d, a, b),
        Ins::Sub(_, a, b) => Ins::Sub(d, a, b),
        Ins::Mul(_, a, b) => Ins::Mul(d, a, b),
        Ins::Neg(_, a) => Ins::Neg(d, a),
        Ins::AddK(_, a, k) => Ins::AddK(d, a, k),
        Ins::KSub(_, a, k) => Ins::KSub(d, a, k),
        Ins::MulK(_, a, k) => Ins::MulK(d, a, k),
        Ins::Const(_, k) => Ins::Const(d, k),
        Ins::LoadCur(_, c) => Ins::LoadCur(d, c),
        Ins::LoadNxt(_, c) => Ins::LoadNxt(d, c),
        Ins::Acc { .. } | Ins::Fold(_) => unreachable!(),
    }
}

/// View the register file as `L` scalars per register.
#[inline]
fn raw_regs_mut(regs: &mut [[PF; U]]) -> &mut [F] {
    const { assert!(size_of::<[PF; U]>() == L * size_of::<F>()) };
    // SAFETY: packed fields are `repr(transparent)` arrays of `F`.
    unsafe { std::slice::from_raw_parts_mut(regs.as_mut_ptr() as *mut F, regs.len() * L) }
}

/// The Montgomery words of a register (`MontyField31` is `repr(transparent)`
/// over `u32`).
#[inline(always)]
fn monty_words(x: &[PF; U]) -> &[u32; L] {
    const { assert!(size_of::<[PF; U]>() == L * 4 && size_of::<F>() == 4) };
    // SAFETY: `[PF; U]` is `L` consecutive `F`, each a `repr(transparent)` `u32`.
    unsafe { &*(x as *const [PF; U] as *const [u32; L]) }
}

#[inline(always)]
fn monty_words_mut(x: &mut [PF; U]) -> &mut [u32; L] {
    // SAFETY: as for `monty_words`; every word written is a valid element.
    unsafe { &mut *(x as *mut [PF; U] as *mut [u32; L]) }
}

#[inline(always)]
fn from_monty(w: u32) -> F {
    debug_assert!(w < P);
    // SAFETY: `F` is `repr(transparent)` over its Montgomery word, `w < p`.
    unsafe { std::mem::transmute::<u32, F>(w) }
}

struct Ctx<'a> {
    rows: &'a [F],
    cur_off: &'a [usize; L],
    nxt_off: &'a [usize; L],
    consts: &'a [F],
    coefs: &'a [[u64; 8]],
}

#[inline(always)]
fn gather(rows: &[F], off: &[usize; L], c: usize, dst: &mut [PF; U]) {
    let dst = monty_words_mut(dst);
    let base = rows.as_ptr() as *const u32;
    for l in 0..L {
        // SAFETY: `eval_combined` checked `off[l] + c < rows.len()` for every
        // offset it builds (row index < rows/width, column < max_col ≤ width).
        dst[l] = unsafe { *base.add(off[l] + c) };
    }
}

#[inline(never)]
fn run(prog: &[Ins], regs: &mut [[PF; U]], ctx: &Ctx, acc: &mut [u64]) {
    macro_rules! bin {
        ($d:expr, $x:expr, $y:expr, $f:expr) => {{
            let (x, y) = ($x, $y);
            regs[$d as usize] = std::array::from_fn(|u| $f(x[u], y[u]));
        }};
    }
    for ins in prog {
        match *ins {
            Ins::Add(d, a, b) => bin!(d, regs[a as usize], regs[b as usize], |x, y| x + y),
            Ins::Sub(d, a, b) => bin!(d, regs[a as usize], regs[b as usize], |x, y| x - y),
            Ins::Mul(d, a, b) => bin!(d, regs[a as usize], regs[b as usize], |x, y| x * y),
            Ins::Neg(d, a) => {
                let x = regs[a as usize];
                regs[d as usize] = std::array::from_fn(|u| -x[u]);
            }
            Ins::AddK(d, a, k) => {
                bin!(d, regs[a as usize], [PF::from(ctx.consts[k as usize]); U], |x, y| x + y)
            }
            Ins::KSub(d, a, k) => {
                bin!(d, [PF::from(ctx.consts[k as usize]); U], regs[a as usize], |x, y| x - y)
            }
            Ins::MulK(d, a, k) => {
                bin!(d, regs[a as usize], [PF::from(ctx.consts[k as usize]); U], |x, y| x * y)
            }
            Ins::Const(d, k) => regs[d as usize] = [PF::from(ctx.consts[k as usize]); U],
            Ins::LoadCur(d, c) => gather(ctx.rows, ctx.cur_off, c as usize, &mut regs[d as usize]),
            Ins::LoadNxt(d, c) => gather(ctx.rows, ctx.nxt_off, c as usize, &mut regs[d as usize]),
            Ins::Acc { g, src, coef } => {
                let v = monty_words(&regs[src as usize]);
                let c = &ctx.coefs[coef as usize];
                let a: &mut [u64; 8 * L] =
                    (&mut acc[g as usize * 8 * L..(g as usize + 1) * 8 * L]).try_into().unwrap();
                for j in 0..8 {
                    let cj = c[j];
                    for l in 0..L {
                        a[j * L + l] += cj * v[l] as u64;
                    }
                }
            }
            Ins::Fold(g) => {
                for a in &mut acc[g as usize * 8 * L..(g as usize + 1) * 8 * L] {
                    *a = (*a & 0xffff_ffff) + (*a >> 32) * R32;
                }
            }
        }
    }
}
