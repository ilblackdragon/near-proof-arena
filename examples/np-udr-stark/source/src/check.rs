//! Debug helpers: evaluate an AIR directly on its traces (no commitments).
//!
//! * [`failing_constraints`] — every `(constraint index, row)` where a
//!   constraint of `Table.constraints` (incl. the bit constraints) is non-zero
//!   (selectors are the exact row indicators, `next` wraps around);
//! * [`bus_imbalance`] — the multiset of `(bus, msg)` with
//!   `Σ send multiplicities ≠ Σ receive multiplicities` (multiplicity
//!   `Σ_k bit_k 2^k`, as in `Interaction.multNat`).
use std::collections::BTreeMap;

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use rayon::prelude::*;

use crate::air::{Air, Expr, Table, Tape};
use crate::field::F;

fn sel(r: usize, n: usize) -> [F; 3] {
    let last = r + 1 == n;
    [F::from_bool(r == 0), F::from_bool(last), F::from_bool(!last)]
}

/// `(constraint, row)` pairs that fail, at most `limit` of them.
pub fn failing_constraints(t: &Table, tr: &RowMajorMatrix<F>, pubs: &[F], limit: usize) -> Vec<(usize, usize)> {
    let tape = Tape::compile(&t.constraints);
    let n = tr.height();
    let w = tr.width();
    let v = &tr.values;
    let mut bad: Vec<(usize, usize)> = (0..n)
        .into_par_iter()
        .flat_map_iter(|r| {
            let mut regs = Vec::with_capacity(tape.ops.len());
            let nx = (r + 1) % n;
            tape.eval(&mut regs, |c, next| v[(if next { nx } else { r }) * w + c], pubs, sel(r, n));
            let out: Vec<(usize, usize)> = tape
                .outputs
                .iter()
                .enumerate()
                .filter(|(_, o)| regs[**o as usize] != F::ZERO)
                .map(|(i, _)| (i, r))
                .collect();
            out
        })
        .collect();
    bad.sort();
    bad.truncate(limit);
    bad
}

/// Bus messages whose send and receive multiplicities differ:
/// `(bus, msg, sent, received)`.
pub fn bus_imbalance(air: &Air, trs: &[RowMajorMatrix<F>], pubs: &[F]) -> Vec<(usize, Vec<u32>, u64, u64)> {
    let mut m: BTreeMap<(usize, Vec<u32>), (u64, u64)> = BTreeMap::new();
    for (t, tr) in air.tables.iter().zip(trs) {
        let (n, w) = (tr.height(), tr.width());
        for it in &t.interactions {
            let exprs: Vec<Expr> = it.mult.iter().chain(&it.msg).cloned().collect();
            let tape = Tape::compile(&exprs);
            let nb = it.mult.len();
            let mut regs = vec![];
            for r in 0..n {
                tape.eval(&mut regs, |c, next| tr.values[(if next { (r + 1) % n } else { r }) * w + c], pubs, sel(r, n));
                let out: Vec<F> = tape.outputs.iter().map(|&o| regs[o as usize]).collect();
                let mult: u64 = (0..nb).map(|k| if out[k] == F::ONE { 1u64 << k } else { 0 }).sum();
                if mult == 0 {
                    continue;
                }
                let msg: Vec<u32> = out[nb..].iter().map(|x| x.as_canonical_u32()).collect();
                let ent = m.entry((it.bus, msg)).or_default();
                if it.send { ent.0 += mult } else { ent.1 += mult }
            }
        }
    }
    m.into_iter().filter(|(_, (s, r))| s != r).map(|((b, msg), (s, r))| (b, msg, s, r)).collect()
}
