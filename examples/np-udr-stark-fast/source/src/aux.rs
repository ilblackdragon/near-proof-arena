//! Grand-product (bus) aux columns, FORMATS.md §3, mirroring
//! `ZkFormal.Stark.Protocol` (`auxCount`, `auxDegree`) and
//! `ZkFormal.Stark.Verifier` (`fingerprint`, `interactionAux`,
//! `auxConstraints`). Group size `auxGroup = 1`.
//!
//! Aux columns (K-valued) of a table, in order:
//! 1. per interaction with `k ≥ 2` multiplicity bits: `P_1..P_{k-1}` then
//!    `Π_1..Π_{k-1}`;
//! 2. one running product per send interaction (group);
//! 3. one running product per receive interaction (group).

use p3_field::PrimeCharacteristicRing;

use crate::air::{Expr, Interaction, Table, Tape};
use crate::field::{EF, F};

pub const AUX_GROUP: usize = 1;

#[derive(Clone, Debug)]
pub struct AuxLayout {
    /// per interaction: number of bits and offset of its chain columns
    pub chain: Vec<(usize, usize)>,
    pub n_chain: usize,
    /// groups of interaction indices: send groups then receive groups
    pub groups: Vec<Vec<usize>>,
    pub send_groups: usize,
    pub recv_groups: usize,
    /// tape over all interaction expressions: for interaction i, outputs
    /// `msg_0..msg_{len-1}, bit_0..bit_{k-1}` consecutively
    pub itape: Tape,
    pub expr_off: Vec<usize>,
}

impl AuxLayout {
    pub fn new(t: &Table) -> AuxLayout {
        let mut chain = vec![];
        let mut off = 0;
        for i in &t.interactions {
            let k = i.mult.len();
            chain.push((k, off));
            if k >= 2 {
                off += 2 * (k - 1);
            }
        }
        let chunk = |send: bool| -> Vec<Vec<usize>> {
            let idx: Vec<usize> = (0..t.interactions.len()).filter(|&j| t.interactions[j].send == send).collect();
            idx.chunks(AUX_GROUP).map(|c| c.to_vec()).collect()
        };
        let sg = chunk(true);
        let rg = chunk(false);
        let (send_groups, recv_groups) = (sg.len(), rg.len());
        let mut groups = sg;
        groups.extend(rg);
        let mut exprs = vec![];
        let mut expr_off = vec![];
        for i in &t.interactions {
            expr_off.push(exprs.len());
            exprs.extend(i.msg.iter().cloned());
            exprs.extend(i.mult.iter().cloned());
        }
        AuxLayout { chain, n_chain: off, groups, send_groups, recv_groups, itape: Tape::compile(&exprs), expr_off }
    }

    pub fn width(&self) -> usize {
        self.n_chain + self.groups.len()
    }
    pub fn num_finals(&self) -> usize {
        self.groups.len()
    }
}

fn dm(i: &Interaction) -> usize {
    i.msg.iter().map(|e| e.degree()).max().unwrap_or(0)
}

fn phi_degree(i: &Interaction) -> usize {
    match i.mult.len() {
        0 => 0,
        1 => i.mult[0].degree() + dm(i),
        _ => 1,
    }
}

/// `Table.auxDegree` (Lean), always ≥ 2.
pub fn aux_degree(t: &Table) -> usize {
    let mut d = 2usize;
    for i in &t.interactions {
        if i.mult.len() >= 2 {
            let b0 = i.mult[0].degree();
            let b1 = i.mult[1].degree();
            let rest = i.mult[2..].iter().map(|b| b.degree() + 2).max().unwrap_or(0);
            d = d.max(2 * dm(i)).max(b0 + dm(i) + b1 + 1).max(rest);
        }
    }
    let lay_groups = |send: bool| -> Vec<usize> {
        let idx: Vec<&Interaction> = t.interactions.iter().filter(|i| i.send == send).collect();
        idx.chunks(AUX_GROUP).map(|g| 2 + g.iter().map(|i| phi_degree(i)).sum::<usize>()).collect()
    };
    for g in lay_groups(true).into_iter().chain(lay_groups(false)) {
        d = d.max(g);
    }
    d
}

/// `Table.degree`: max(2, allConstraints degrees, aux degree).
pub fn table_degree(t: &Table) -> usize {
    t.constraints.iter().map(|c| c.degree()).max().unwrap_or(0).max(2).max(aux_degree(t))
}

/// Booleanity constraints `b·(b + (−1))` of all multiplicity bits
/// (`Table.bitConstraints`), for Rust-built tables.
pub fn bit_constraints(t: &Table) -> Vec<Expr> {
    t.interactions
        .iter()
        .flat_map(|i| i.mult.iter().map(|b| Expr::mul(b.clone(), Expr::add(b.clone(), Expr::neg(Expr::Const(1))))))
        .collect()
}

/// Fingerprint `(bus+1)·α^len + Σ_k msg_k·α^k`.
#[inline]
pub fn fingerprint(bus: usize, msg: &[EF], alpha: EF) -> EF {
    let mut acc = EF::ZERO;
    let mut pw = EF::ONE;
    for m in msg {
        acc += pw * *m;
        pw *= alpha;
    }
    acc + pw * F::from_u64(bus as u64 + 1)
}

/// Values of the interaction expressions on one row: `vals` = itape
/// registers' outputs (as EF), per interaction `(msg, bits)`.
/// Computes the per-interaction factor `φ_i` and pushes the chain
/// constraints (if `out` is given) — exactly `interactionAux`.
pub fn chain_and_phi(
    t: &Table,
    lay: &AuxLayout,
    ivals: &[EF],
    alpha: EF,
    gamma: EF,
    aux: &[EF],
    mut out: Option<&mut Vec<EF>>,
    phis: &mut Vec<EF>,
) {
    phis.clear();
    for (ii, i) in t.interactions.iter().enumerate() {
        let o = lay.expr_off[ii];
        let msg = &ivals[o..o + i.msg.len()];
        let bits = &ivals[o + i.msg.len()..o + i.msg.len() + i.mult.len()];
        let p0 = gamma - fingerprint(i.bus, msg, alpha);
        let k = bits.len();
        match k {
            0 => phis.push(EF::ONE),
            1 => phis.push(EF::ONE + bits[0] * (p0 - EF::ONE)),
            _ => {
                let off = lay.chain[ii].1;
                let ps = &aux[off..off + k - 1];
                let pis = &aux[off + k - 1..off + 2 * (k - 1)];
                if let Some(out) = out.as_deref_mut() {
                    for j in 0..k - 1 {
                        let prev = if j == 0 { p0 } else { ps[j - 1] };
                        out.push(ps[j] - prev * prev);
                    }
                    for j in 0..k - 1 {
                        let prev = if j == 0 { EF::ONE + bits[0] * (p0 - EF::ONE) } else { pis[j - 1] };
                        let fac = EF::ONE + bits[j + 1] * (ps[j] - EF::ONE);
                        out.push(pis[j] - prev * fac);
                    }
                }
                phis.push(pis[k - 2]);
            }
        }
    }
}

/// Aux constraints of a table (`auxConstraints`), appended to `out`.
#[allow(clippy::too_many_arguments)]
pub fn aux_constraints(
    t: &Table,
    lay: &AuxLayout,
    ivals: &[EF],
    alpha: EF,
    gamma: EF,
    aux: &[EF],
    aux_next: &[EF],
    fins: &[EF],
    sel: [EF; 3],
    out: &mut Vec<EF>,
    phis: &mut Vec<EF>,
) {
    chain_and_phi(t, lay, ivals, alpha, gamma, aux, Some(out), phis);
    for (g, grp) in lay.groups.iter().enumerate() {
        let phi = grp.iter().fold(EF::ONE, |a, &i| a * phis[i]);
        let a = aux[lay.n_chain + g];
        let an = aux_next[lay.n_chain + g];
        out.push(sel[0] * (a - EF::ONE));
        out.push(sel[2] * (an - a * phi));
        out.push(sel[1] * (a * phi - fins[g]));
    }
}
