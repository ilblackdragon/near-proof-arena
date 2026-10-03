//! Mixed-height wide-digest Merkle commitment (MMCS), DESIGN.md §4.
//!
//! A commitment covers a list of matrices whose heights are powers of two,
//! the largest being `H0 = 2^L`. Let `rows_k(j)` be the concatenation, in
//! matrix order, of row `j` of every matrix of height `H0 / 2^k`, each base
//! element as 4 LE bytes (empty if there is no such matrix — then the leaf
//! term is omitted, see below).
//!
//! * level 0: `N_0[j] = WH(LEAF, rows_0(j))`
//! * level k ≥ 1: `N_k[j] = WH(NODE, u8(k) ‖ N_{k-1}[2j] ‖ N_{k-1}[2j+1] ‖ X)`
//!   where `X = WH(LEAF, rows_k(j))` if some matrix has height `H0/2^k`, else
//!   `X` is empty.
//! * root `= N_L[0]`.
//!
//! "Some matrix has height" includes matrices of width 0 (their rows are
//! empty but they still create the `X` term).
//!
//! Multiproof for level-0 query indices `J` (any order, duplicates allowed):
//! `S_0 = sort(dedup(J))`, `S_k = sort(dedup({j >> 1 | j ∈ S_{k-1}}))`.
//! * `rows`: for each matrix `m` (matrix order), for each `j ∈ S_{k_m}`
//!   ascending, its row (`width_m` field elements);
//! * `siblings`: for k = 1..=L, for j ∈ S_k ascending, for c in [2j, 2j+1]:
//!   if `c ∉ S_{k-1}`, the digest `N_{k-1}[c]`, in that order.

use rayon::prelude::*;

use crate::field::F;
use crate::hash::{wh, Digest64, TAG_LEAF, TAG_NODE};
use p3_field::PrimeField32;

/// One committed matrix. `values` is row-major. If `bitrev` is set, leaf `j`
/// of the tree is stored row `bitrev(j)` (used for LDE matrices kept in
/// natural order).
pub struct Mat {
    pub width: usize,
    pub log_height: usize,
    pub values: Vec<F>,
    pub bitrev: bool,
}

impl Mat {
    #[inline]
    pub fn height(&self) -> usize {
        1 << self.log_height
    }
    #[inline]
    pub fn row(&self, j: usize) -> &[F] {
        let r = if self.bitrev { rev(j, self.log_height) } else { j };
        &self.values[r * self.width..(r + 1) * self.width]
    }
}

#[inline]
pub fn rev(j: usize, bits: usize) -> usize {
    if bits == 0 { 0 } else { j.reverse_bits() >> (usize::BITS as usize - bits) }
}

fn put_row(buf: &mut Vec<u8>, row: &[F]) {
    for x in row {
        buf.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
    }
}

/// Hash `rows_k(j)` for the given matrices (all of the same height).
fn leaf_hash(mats: &[&Mat], j: usize, buf: &mut Vec<u8>) -> Digest64 {
    buf.clear();
    for m in mats {
        put_row(buf, m.row(j));
    }
    wh(TAG_LEAF, &[buf])
}

fn node_hash(k: usize, l: &Digest64, r: &Digest64, x: Option<&Digest64>) -> Digest64 {
    match x {
        Some(x) => wh(TAG_NODE, &[&[k as u8], l, r, x]),
        None => wh(TAG_NODE, &[&[k as u8], l, r]),
    }
}

pub struct Tree {
    pub log_h0: usize,
    /// `levels[k][j] = N_k[j]`.
    pub levels: Vec<Vec<Digest64>>,
}

impl Tree {
    pub fn root(&self) -> Digest64 {
        self.levels[self.log_h0][0]
    }
}

pub fn log_h0(mats: &[Mat]) -> usize {
    mats.iter().map(|m| m.log_height).max().expect("no matrices")
}

pub fn commit(mats: &[Mat]) -> Tree {
    let l0 = log_h0(mats);
    let at = |k: usize| -> Vec<&Mat> { mats.iter().filter(|m| m.log_height + k == l0).collect() };
    let m0 = at(0);
    let lvl0: Vec<Digest64> = (0..1usize << l0)
        .into_par_iter()
        .map_init(Vec::new, |buf, j| leaf_hash(&m0, j, buf))
        .collect();
    let mut levels = vec![lvl0];
    for k in 1..=l0 {
        let mk = at(k);
        let prev = &levels[k - 1];
        let has = !mk.is_empty();
        let lvl: Vec<Digest64> = (0..1usize << (l0 - k))
            .into_par_iter()
            .map_init(Vec::new, |buf, j| {
                let x = if has { Some(leaf_hash(&mk, j, buf)) } else { None };
                node_hash(k, &prev[2 * j], &prev[2 * j + 1], x.as_ref())
            })
            .collect();
        levels.push(lvl);
    }
    Tree { log_h0: l0, levels }
}

/// The sorted, deduplicated index sets `S_0..=S_L`.
pub fn index_sets(log_h0: usize, idx: &[usize]) -> Vec<Vec<usize>> {
    let mut s0: Vec<usize> = idx.to_vec();
    s0.sort_unstable();
    s0.dedup();
    let mut out = vec![s0];
    for k in 1..=log_h0 {
        let mut s: Vec<usize> = out[k - 1].iter().map(|j| j >> 1).collect();
        s.dedup();
        out.push(s);
    }
    out
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Opening {
    /// Per matrix, the opened rows concatenated (|S_{k_m}| · width_m values).
    pub rows: Vec<Vec<F>>,
    pub siblings: Vec<Digest64>,
}

pub fn open(mats: &[Mat], tree: &Tree, idx: &[usize]) -> Opening {
    let l0 = tree.log_h0;
    let sets = index_sets(l0, idx);
    let rows = mats
        .iter()
        .map(|m| {
            let k = l0 - m.log_height;
            let mut r = Vec::with_capacity(sets[k].len() * m.width);
            for &j in &sets[k] {
                r.extend_from_slice(m.row(j));
            }
            r
        })
        .collect();
    let mut siblings = vec![];
    for k in 1..=l0 {
        let below = &sets[k - 1];
        for &j in &sets[k] {
            for c in [2 * j, 2 * j + 1] {
                if below.binary_search(&c).is_err() {
                    siblings.push(tree.levels[k - 1][c]);
                }
            }
        }
    }
    Opening { rows, siblings }
}

/// Shape of a commitment as known to the verifier: `(width, log_height)` per
/// matrix.
pub type Shape = Vec<(usize, usize)>;

/// Number of siblings the multiproof for `idx` contains.
pub fn num_siblings(log_h0: usize, idx: &[usize]) -> usize {
    let sets = index_sets(log_h0, idx);
    let mut n = 0;
    for k in 1..=log_h0 {
        for &j in &sets[k] {
            for c in [2 * j, 2 * j + 1] {
                if sets[k - 1].binary_search(&c).is_err() {
                    n += 1;
                }
            }
        }
    }
    n
}

/// Verify a multiproof. Returns `false` on any shape mismatch.
pub fn verify(shape: &Shape, root: &Digest64, idx: &[usize], op: &Opening) -> bool {
    let Some(l0) = shape.iter().map(|s| s.1).max() else { return false };
    if op.rows.len() != shape.len() {
        return false;
    }
    let sets = index_sets(l0, idx);
    for (m, (w, lh)) in shape.iter().enumerate() {
        if op.rows[m].len() != sets[l0 - lh].len() * w {
            return false;
        }
    }
    // rows_k(j) bytes for the j-th element (position p) of S_k.
    let leaf = |k: usize, p: usize, buf: &mut Vec<u8>| -> Option<Digest64> {
        let mut any = false;
        buf.clear();
        for (m, (w, lh)) in shape.iter().enumerate() {
            if lh + k == l0 {
                any = true;
                put_row(buf, &op.rows[m][p * w..(p + 1) * w]);
            }
        }
        if any { Some(wh(TAG_LEAF, &[buf])) } else { None }
    };
    let mut buf = vec![];
    let mut cur: Vec<Digest64> = Vec::with_capacity(sets[0].len());
    for p in 0..sets[0].len() {
        match leaf(0, p, &mut buf) {
            Some(d) => cur.push(d),
            None => return false,
        }
    }
    let mut sib = op.siblings.iter();
    for k in 1..=l0 {
        let below = &sets[k - 1];
        let mut next = Vec::with_capacity(sets[k].len());
        for (p, &j) in sets[k].iter().enumerate() {
            let mut ch = [[0u8; 64]; 2];
            for (i, c) in [2 * j, 2 * j + 1].into_iter().enumerate() {
                ch[i] = match below.binary_search(&c) {
                    Ok(q) => cur[q],
                    Err(_) => match sib.next() {
                        Some(d) => *d,
                        None => return false,
                    },
                };
            }
            let x = leaf(k, p, &mut buf);
            next.push(node_hash(k, &ch[0], &ch[1], x.as_ref()));
        }
        cur = next;
    }
    sib.next().is_none() && cur.len() == 1 && &cur[0] == root
}

#[cfg(test)]
mod tests {
    use super::*;
    use p3_field::PrimeCharacteristicRing;

    fn mats() -> Vec<Mat> {
        let mk = |w: usize, lh: usize, seed: u32, bitrev| Mat {
            width: w,
            log_height: lh,
            values: (0..(w << lh) as u32).map(|i| F::new(i * 7 + seed)).collect(),
            bitrev,
        };
        vec![mk(3, 5, 1, true), mk(2, 3, 2, false), mk(0, 3, 0, false), mk(1, 5, 9, false), mk(4, 0, 3, false)]
    }

    #[test]
    fn roundtrip_and_tamper() {
        let ms = mats();
        let t = commit(&ms);
        let shape: Shape = ms.iter().map(|m| (m.width, m.log_height)).collect();
        let idx = vec![31, 0, 5, 5, 17, 16];
        let mut op = open(&ms, &t, &idx);
        assert_eq!(op.siblings.len(), num_siblings(5, &idx));
        assert!(verify(&shape, &t.root(), &idx, &op));
        op.rows[1][0] += F::ONE;
        assert!(!verify(&shape, &t.root(), &idx, &op));
        op.rows[1][0] -= F::ONE;
        op.siblings[2][5] ^= 1;
        assert!(!verify(&shape, &t.root(), &idx, &op));
        op.siblings[2][5] ^= 1;
        op.siblings.push([0; 64]);
        assert!(!verify(&shape, &t.root(), &idx, &op));
    }
}
