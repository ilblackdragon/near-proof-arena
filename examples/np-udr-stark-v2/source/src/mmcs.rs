//! Mixed-height wide-digest Merkle commitment (MMCS), DESIGN.md §4.
//!
//! A commitment covers a list of matrices whose heights are powers of two,
//! the largest being `H0 = 2^L`. Let `rows_k(j)` be the concatenation, in
//! matrix order, of row `j` of every matrix of height `H0 / 2^k`, each base
//! element as 4 LE bytes (empty if there is no such matrix — then the leaf
//! term is omitted, see below).
//!
//! * level 0: `N_0[j] = WH(LEAF, rows_0(j))`
//! * level k ≥ 1: `N_k[j] = WH(NODE, u8(k) ‖ N_{k-1}[2j] ‖ N_{k-1}[2j+1] ‖ rows_k(j))`
//!   (rows inlined; empty if no matrix has height `H0/2^k`).
//! * root `= N_L[0]`.
//!
//! Multiproof for level-0 query indices `J` (any order, duplicates allowed):
//! `S_0 = sort(dedup(J))`, `S_k = sort(dedup({j >> 1 | j ∈ S_{k-1}}))`.
//! * `rows`: for each matrix `m` (matrix order), for each `j ∈ S_{k_m}`
//!   ascending, its row (`width_m` field elements);
//! * `siblings`: for k = 1..=L, for j ∈ S_k ascending, for c in [2j, 2j+1]:
//!   if `c ∉ S_{k-1}`, the digest `N_{k-1}[c]`, in that order.

use rayon::prelude::*;

use crate::field::F;
use crate::hash::{Digest64, TAG_LEAF, TAG_NODE, wh};
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
        let r = if self.bitrev {
            rev(j, self.log_height)
        } else {
            j
        };
        &self.values[r * self.width..(r + 1) * self.width]
    }
}

#[inline]
pub fn rev(j: usize, bits: usize) -> usize {
    if bits == 0 {
        0
    } else {
        j.reverse_bits() >> (usize::BITS as usize - bits)
    }
}

fn put_row(buf: &mut Vec<u8>, row: &[F]) {
    for x in row {
        buf.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
    }
}

/// `rows(j)` bytes for the given matrices (all of one height).
fn rows_bytes(mats: &[&Mat], j: usize, buf: &mut Vec<u8>) {
    buf.clear();
    for m in mats {
        put_row(buf, m.row(j));
    }
}

pub fn node_hash(k: usize, l: &Digest64, r: &Digest64, rows: &[u8]) -> Digest64 {
    wh(TAG_NODE, &[&[k as u8], l, r, rows])
}

/// Leaf hash `WH(LEAF, rows)` from row slices.
pub fn hash_rows(rows: &[&[F]], buf: &mut Vec<u8>) -> Digest64 {
    buf.clear();
    for r in rows {
        put_row(buf, r);
    }
    wh(TAG_LEAF, &[buf])
}

/// Node hash with inlined injected rows.
pub fn hash_node_rows(
    k: usize,
    l: &Digest64,
    r: &Digest64,
    rows: &[&[F]],
    buf: &mut Vec<u8>,
) -> Digest64 {
    buf.clear();
    for x in rows {
        put_row(buf, x);
    }
    node_hash(k, l, r, buf)
}

/// Level `k` without injected matrices.
pub fn plain_level(k: usize, prev: &[Digest64]) -> Vec<Digest64> {
    (0..prev.len() / 2)
        .into_par_iter()
        .map(|j| node_hash(k, &prev[2 * j], &prev[2 * j + 1], &[]))
        .collect()
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
    mats.iter()
        .map(|m| m.log_height)
        .max()
        .expect("no matrices")
}

pub fn commit(mats: &[Mat]) -> Tree {
    let l0 = log_h0(mats);
    let at = |k: usize| -> Vec<&Mat> { mats.iter().filter(|m| m.log_height + k == l0).collect() };
    let m0 = at(0);
    let lvl0: Vec<Digest64> = (0..1usize << l0)
        .into_par_iter()
        .map_init(Vec::new, |buf, j| {
            rows_bytes(&m0, j, buf);
            wh(TAG_LEAF, &[buf])
        })
        .collect();
    let mut levels = vec![lvl0];
    for k in 1..=l0 {
        let mk = at(k);
        let prev = &levels[k - 1];
        let lvl: Vec<Digest64> = (0..1usize << (l0 - k))
            .into_par_iter()
            .map_init(Vec::new, |buf, j| {
                rows_bytes(&mk, j, buf);
                node_hash(k, &prev[2 * j], &prev[2 * j + 1], buf)
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
    Opening {
        rows,
        siblings: siblings(tree, idx),
    }
}

/// The sibling stream of the multiproof for `idx`.
pub fn siblings(tree: &Tree, idx: &[usize]) -> Vec<Digest64> {
    let l0 = tree.log_h0;
    let sets = index_sets(l0, idx);
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
    siblings
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
    let Some(l0) = shape.iter().map(|s| s.1).max() else {
        return false;
    };
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
    let rows = |k: usize, p: usize, buf: &mut Vec<u8>| -> bool {
        let mut any = false;
        buf.clear();
        for (m, (w, lh)) in shape.iter().enumerate() {
            if lh + k == l0 {
                any = true;
                put_row(buf, &op.rows[m][p * w..(p + 1) * w]);
            }
        }
        any
    };
    let mut buf = vec![];
    let mut cur: Vec<Digest64> = Vec::with_capacity(sets[0].len());
    for p in 0..sets[0].len() {
        if !rows(0, p, &mut buf) {
            return false;
        }
        cur.push(wh(TAG_LEAF, &[&buf]));
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
            rows(k, p, &mut buf);
            next.push(node_hash(k, &ch[0], &ch[1], &buf));
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
            values: (0..(w << lh) as u32)
                .map(|i| F::new(i * 7 + seed))
                .collect(),
            bitrev,
        };
        vec![
            mk(3, 5, 1, true),
            mk(2, 3, 2, false),
            mk(0, 3, 0, false),
            mk(1, 5, 9, false),
            mk(4, 0, 3, false),
        ]
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

// ---------------------------------------------------------------------------
// Wire form of a multiproof (FORMATS.md §5): leaves `rows_0(j)` for `j ∈ S_0`
// ascending; then for each level k = 1..=L and parent p ∈ S_k ascending: the
// missing child digest (if exactly one child is in S_{k-1}), then
// `rows_k(p)` if level k has matrices. `shape` is `(log, width)` per matrix.
// ---------------------------------------------------------------------------

fn level_mats(shape: &[(usize, usize)], l0: usize, k: usize) -> Vec<usize> {
    (0..shape.len()).filter(|&m| shape[m].0 + k == l0).collect()
}

pub fn write_opening(out: &mut Vec<u8>, shape: &[(usize, usize)], idx: &[usize], op: &Opening) {
    let l0 = shape.iter().map(|s| s.0).max().unwrap();
    let sets = index_sets(l0, idx);
    let rows_at = |out: &mut Vec<u8>, k: usize, pos: usize| {
        for m in level_mats(shape, l0, k) {
            let w = shape[m].1;
            put_row(out, &op.rows[m][pos * w..(pos + 1) * w]);
        }
    };
    for p in 0..sets[0].len() {
        rows_at(out, 0, p);
    }
    let mut sib = op.siblings.iter();
    for k in 1..=l0 {
        for (p, &j) in sets[k].iter().enumerate() {
            let a = sets[k - 1].binary_search(&(2 * j)).is_ok();
            let b = sets[k - 1].binary_search(&(2 * j + 1)).is_ok();
            if !(a && b) {
                out.extend_from_slice(sib.next().expect("sibling"));
            }
            rows_at(out, k, p);
        }
    }
}

pub fn read_opening(
    r: &mut crate::protocol::Reader,
    shape: &[(usize, usize)],
    idx: &[usize],
) -> Option<Opening> {
    let l0 = shape.iter().map(|s| s.0).max()?;
    let sets = index_sets(l0, idx);
    let mut rows: Vec<Vec<F>> = shape.iter().map(|_| vec![]).collect();
    let mut read_rows = |r: &mut crate::protocol::Reader, k: usize| -> Option<()> {
        for m in level_mats(shape, l0, k) {
            for _ in 0..shape[m].1 {
                rows[m].push(r.f()?);
            }
        }
        Some(())
    };
    for _ in 0..sets[0].len() {
        read_rows(r, 0)?;
    }
    let mut siblings = vec![];
    for k in 1..=l0 {
        for &j in &sets[k] {
            let a = sets[k - 1].binary_search(&(2 * j)).is_ok();
            let b = sets[k - 1].binary_search(&(2 * j + 1)).is_ok();
            if !(a && b) {
                siblings.push(r.d64()?);
            }
            read_rows(r, k)?;
        }
    }
    Some(Opening { rows, siblings })
}
