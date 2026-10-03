//! Concrete (native) evaluation of the AIRs on a trace.
//!
//! [`Concrete`] implements `AirBuilder + InteractionBuilder` over the base
//! field itself: evaluating an AIR on two concrete rows yields the values of
//! every constraint and every bus interaction `(bus, tuple, count)`.
//!
//! Used for
//! * computing provider multiplicities (lookup tallies) during proving,
//! * the prover's self-check (`check_all`: every constraint vanishes, every
//!   permutation bus balances, every lookup query hits a provided entry),
//! * the witness-mutation tool (`bin/mutate.rs`).

use crate::air::NpAir;
use crate::config::Val;
use crate::consts::{LOOKUP_BUSES, PERM_BUSES};
use p3_air::{Air, AirBuilder, BaseAir, RowWindow};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use std::collections::HashMap;

pub struct Concrete<'a> {
    pub cur: &'a [Val],
    pub nxt: &'a [Val],
    pub pre: RowWindow<'a, Val>,
    pub pvs: &'a [Val],
    pub first: bool,
    pub last: bool,
    /// Index of the next constraint; failing indices are collected.
    pub idx: usize,
    pub failed: Vec<usize>,
    pub record_inter: bool,
    pub inter: Vec<(&'static str, Vec<Val>, Val, u32)>,
}

fn intern(bus: &str) -> &'static str {
    for b in PERM_BUSES.iter().chain(LOOKUP_BUSES.iter()) {
        if *b == bus {
            return b;
        }
    }
    panic!("unknown bus {bus}")
}

impl<'a> AirBuilder for Concrete<'a> {
    type F = Val;
    type Expr = Val;
    type Var = Val;
    type PreprocessedWindow = RowWindow<'a, Val>;
    type MainWindow = RowWindow<'a, Val>;
    type PublicVar = Val;
    type PeriodicVar = Val;

    fn main(&self) -> Self::MainWindow {
        RowWindow::from_two_rows(self.cur, self.nxt)
    }
    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        &self.pre
    }
    fn is_first_row(&self) -> Val {
        if self.first { Val::ONE } else { Val::ZERO }
    }
    fn is_last_row(&self) -> Val {
        if self.last { Val::ONE } else { Val::ZERO }
    }
    fn is_transition(&self) -> Val {
        if self.last { Val::ZERO } else { Val::ONE }
    }
    fn assert_zero<I: Into<Val>>(&mut self, x: I) {
        if x.into() != Val::ZERO {
            self.failed.push(self.idx);
        }
        self.idx += 1;
    }
    fn public_values(&self) -> &[Val] {
        self.pvs
    }
}

impl InteractionBuilder for Concrete<'_> {
    fn push_interaction<E: Into<Val>>(
        &mut self,
        bus_name: &str,
        fields: impl IntoIterator<Item = E>,
        count: impl Into<Count<Val>>,
    ) {
        if !self.record_inter {
            return;
        }
        let (c, w) = count.into().into_parts();
        if c == Val::ZERO && w != 0 {
            return;
        }
        let f: Vec<Val> = fields.into_iter().map(Into::into).collect();
        self.inter.push((intern(bus_name), f, c, w));
    }
    fn push_local_interaction(&mut self, _t: impl IntoIterator<Item = (Vec<Val>, Count<Val>)>) {
        unimplemented!("no local interactions")
    }
}

/// Per-row evaluation result.
pub struct RowEval {
    pub failed: Vec<usize>,
    /// (bus, tuple, count, weight); weight 0 = lookup table entry (recorded
    /// even with multiplicity 0), weight 1 = query / perm send / receive.
    pub inter: Vec<(&'static str, Vec<Val>, Val, u32)>,
}

pub fn eval_row(
    air: &NpAir,
    trace: &RowMajorMatrix<Val>,
    pre: Option<&RowMajorMatrix<Val>>,
    pvs: &[Val],
    row: usize,
    record_inter: bool,
) -> RowEval {
    let h = trace.height();
    let w = trace.width();
    let nr = (row + 1) % h;
    let cur = &trace.values[row * w..(row + 1) * w];
    let nxt = &trace.values[nr * w..(nr + 1) * w];
    let (pc, pn): (&[Val], &[Val]) = match pre {
        Some(p) => {
            let pw = p.width();
            (&p.values[row * pw..(row + 1) * pw], &p.values[nr * pw..(nr + 1) * pw])
        }
        None => (&[], &[]),
    };
    eval_pair(air, cur, nxt, pc, pn, pvs, row == 0, row + 1 == h, record_inter)
}

/// Evaluate the AIR on an explicit (current, next) row pair.
#[allow(clippy::too_many_arguments)]
pub fn eval_pair(
    air: &NpAir,
    cur: &[Val],
    nxt: &[Val],
    pre_cur: &[Val],
    pre_nxt: &[Val],
    pvs: &[Val],
    first: bool,
    last: bool,
    record_inter: bool,
) -> RowEval {
    let mut b = Concrete {
        cur,
        nxt,
        pre: RowWindow::from_two_rows(pre_cur, pre_nxt),
        pvs,
        first,
        last,
        idx: 0,
        failed: Vec::new(),
        record_inter,
        inter: Vec::new(),
    };
    air.eval(&mut b);
    RowEval { failed: b.failed, inter: b.inter }
}

pub type Key = (&'static str, Vec<u32>);

pub fn key(bus: &'static str, t: &[Val]) -> Key {
    (bus, t.iter().map(|x| x.as_canonical_u32()).collect())
}

/// Lookup query tally: (bus, tuple) -> total query count.
#[derive(Default)]
pub struct Tally(pub HashMap<Key, u64>);

impl Tally {
    pub fn get(&self, bus: &'static str, t: &[u32]) -> u64 {
        self.0.get(&(bus, t.to_vec())).copied().unwrap_or(0)
    }
}

/// Collect lookup queries (positive counts on lookup buses) of `air`'s rows.
pub fn tally_queries(
    air: &NpAir,
    trace: &RowMajorMatrix<Val>,
    pvs: &[Val],
    rows: core::ops::Range<usize>,
    tally: &mut Tally,
) {
    for row in rows {
        let e = eval_row(air, trace, None, pvs, row, true);
        for (bus, t, c, w) in e.inter {
            if w != 0 && LOOKUP_BUSES.contains(&bus) {
                let cu = c.as_canonical_u32();
                if cu < (1 << 30) {
                    *tally.0.entry(key(bus, &t)).or_insert(0) += cu as u64;
                }
            }
        }
    }
}

/// Full check of a set of traces: constraints on every row and bus balance.
/// Returns human-readable problems (empty = consistent).
pub struct CheckReport {
    pub constraint_failures: Vec<(String, usize, Vec<usize>)>,
    pub bus_problems: Vec<String>,
}

impl CheckReport {
    pub fn ok(&self) -> bool {
        self.constraint_failures.is_empty() && self.bus_problems.is_empty()
    }
}

pub fn check_all(
    airs: &[NpAir],
    traces: &[RowMajorMatrix<Val>],
    pvs: &[Val],
    max_failures: usize,
) -> CheckReport {
    use p3_maybe_rayon::prelude::*;
    let mut constraint_failures = Vec::new();
    let mut sums: HashMap<Key, i64> = HashMap::new();
    for (air, trace) in airs.iter().zip(traces) {
        let pre: Option<RowMajorMatrix<Val>> = BaseAir::<Val>::preprocessed_trace(air);
        let pv_slice: &[Val] = if air.num_pv() > 0 { pvs } else { &[] };
        let h = trace.height();
        let evals: Vec<RowEval> = (0..h)
            .into_par_iter()
            .map(|row| eval_row(air, trace, pre.as_ref(), pv_slice, row, true))
            .collect();
        for (row, e) in evals.into_iter().enumerate() {
            if !e.failed.is_empty() && constraint_failures.len() < max_failures {
                constraint_failures.push((air.name().to_string(), row, e.failed.clone()));
            }
            for (bus, t, c, _w) in e.inter {
                let cu = c.as_canonical_u32();
                let signed =
                    if cu > Val::ORDER_U32 / 2 { -((Val::ORDER_U32 - cu) as i64) } else { cu as i64 };
                *sums.entry(key(bus, &t)).or_insert(0) += signed;
            }
        }
    }
    let mut bus_problems = Vec::new();
    for (k, s) in &sums {
        if *s != 0 && bus_problems.len() < max_failures {
            let kind = if LOOKUP_BUSES.contains(&k.0) { "lookup" } else { "perm" };
            bus_problems.push(format!("{kind} imbalance on {}: {:?} (net {s})", k.0, k.1));
        }
    }
    bus_problems.sort();
    CheckReport { constraint_failures, bus_problems }
}
