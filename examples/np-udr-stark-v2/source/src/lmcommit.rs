//! Streaming MMCS commitment and opening for the low-memory prover.
//!
//! Same commitment as [`crate::mmcs`] (bit for bit): level 0
//! `WH(LEAF, rows_0(j))`, level `k ≥ 1` `WH(NODE, u8 k ‖ L ‖ R ‖ rows_k(j))`.
//! Rows are never materialized for a whole matrix: level-0 positions are
//! processed in groups, each matrix's columns in chunks (coefficients
//! recomputed per group), evaluated on the group's position range with
//! [`eval_range`] and streamed into a [`WhStream`].
//!
//! Levels below `KEEP` are not stored; an opening recomputes the
//! `2^KEEP`-leaf subtree around every queried position from the matrix rows
//! on that range.

use std::collections::HashMap;

use p3_field::PrimeField32;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;

use crate::field::F;
use crate::hash::{Digest64, TAG_LEAF, TAG_NODE, wh};
use crate::lmsrc::Src;
use crate::lowmem::{Dft, WhStream, eval_range};
use crate::mmcs::{Opening, index_sets};

/// Levels `< keep` are recomputed at opening time: `KEEP` normally,
/// `KEEP_LARGE` for traces under memory pressure (4× smaller stored trees,
/// costlier openings).
pub const KEEP: usize = 4;
pub const KEEP_LARGE: usize = 6;

/// A committed matrix: its source, LDE log, coset shift and tree class
/// (`l0 − lde log`).
pub struct CMat<'a> {
    pub src: &'a Src<'a>,
    pub lde: usize,
    pub shift: F,
    pub class: usize,
}

pub struct LTree {
    pub l0: usize,
    /// `levels[k]` for `k ≥ KEEP` (or every level when the tree is small)
    pub levels: Vec<Option<Vec<Digest64>>>,
}

impl LTree {
    pub fn root(&self) -> Digest64 {
        self.levels[self.l0].as_ref().unwrap()[0]
    }
}

/// Hash level `k` on the position ranges `ranges` (`(p0, len)` at level `k`),
/// given the children digests `prev` (concatenated in range order, `2·Σlen`
/// entries) for `k ≥ 1`. Returns the digests in range order.
pub fn hash_ranges(
    dft: &Dft,
    mats: &[CMat],
    k: usize,
    ranges: &[(usize, usize)],
    prev: Option<&[Digest64]>,
    chunk: usize,
) -> Vec<Digest64> {
    let n: usize = ranges.iter().map(|r| r.1).sum();
    let ms: Vec<&CMat> = mats.iter().filter(|m| m.class == k).collect();
    if ms.is_empty() {
        let p = prev.expect("level 0 needs a matrix");
        return (0..n)
            .map(|i| wh(TAG_NODE, &[&[k as u8], &p[2 * i], &p[2 * i + 1]]))
            .collect();
    }
    let mut st = WhStream::new(n, if k == 0 { TAG_LEAF } else { TAG_NODE });
    if let Some(p) = prev {
        st.feed(129, |i, out| {
            out.push(k as u8);
            out.extend_from_slice(&p[2 * i]);
            out.extend_from_slice(&p[2 * i + 1]);
        });
    }
    for m in &ms {
        for (c0, c1) in m.src.chunks(chunk) {
            let co = m.src.coeffs(dft, c0, c1);
            let w = c1 - c0;
            let mut off = 0;
            for &(p0, len) in ranges {
                let t = co.height();
                // evaluate block by block to bound the buffer
                let step = len.min(t);
                for b in 0..len / step {
                    let e = eval_range(dft, &co, m.lde, m.shift, p0 + b * step, step, None);
                    st.feed_at(
                        off + b * step,
                        4 * w,
                        |i, out| {
                            for x in &e.values[i * w..(i + 1) * w] {
                                out.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
                            }
                        },
                        step,
                    );
                }
                off += len;
            }
            st.commit_len(4 * w);
        }
    }
    st.finish()
}

/// Commit a round. `group` = level-0 positions hashed at once.
pub fn commit(
    dft: &Dft,
    mats: &[CMat],
    l0: usize,
    group: usize,
    chunk: usize,
    keep_lvl: usize,
) -> LTree {
    let n0 = 1usize << l0;
    let s = group.min(n0);
    let ls = p3_util::log2_strict_usize(s);
    let keep = if l0 < 12 { 0 } else { keep_lvl };
    let mut levels: Vec<Option<Vec<Digest64>>> = (0..=l0)
        .map(|k| {
            if k >= keep {
                Some(Vec::with_capacity(n0 >> k))
            } else {
                None
            }
        })
        .collect();
    for g in 0..n0 / s {
        let mut cur = hash_ranges(dft, mats, 0, &[(g * s, s)], None, chunk);
        if keep == 0 {
            levels[0].as_mut().unwrap().extend_from_slice(&cur);
        }
        for k in 1..=ls {
            cur = hash_ranges(dft, mats, k, &[((g * s) >> k, s >> k)], Some(&cur), chunk);
            if k >= keep {
                levels[k].as_mut().unwrap().extend_from_slice(&cur);
            }
        }
    }
    for k in ls + 1..=l0 {
        let prev = levels[k - 1].take().unwrap();
        let cur = hash_ranges(dft, mats, k, &[(0, n0 >> k)], Some(&prev), chunk);
        levels[k - 1] = Some(prev);
        levels[k] = Some(cur);
    }
    LTree { l0, levels }
}

/// Rows of every matrix at the positions of `ranges` (`(p0, len)` at the
/// matrix's level), concatenated per matrix.
fn rows_on(dft: &Dft, m: &CMat, ranges: &[(usize, usize)], chunk: usize) -> Vec<Vec<F>> {
    let w = m.src.width();
    let n: usize = ranges.iter().map(|r| r.1).sum();
    let mut out = vec![vec![F::default(); w]; n];
    for (c0, c1) in m.src.chunks(chunk) {
        let co = m.src.coeffs(dft, c0, c1);
        let cw = c1 - c0;
        // ranges grouped by length; one streaming pass per length
        let mut lens: Vec<usize> = ranges.iter().map(|r| r.1).collect();
        lens.sort_unstable();
        lens.dedup();
        let mut evs: Vec<Option<RowMajorMatrix<F>>> = ranges.iter().map(|_| None).collect();
        // Small tables: evaluating the whole coset blocks (size T) that hold
        // the ranges (~log T operations per point) is cheaper than one fold
        // over all coefficients per range (T per range)
        let t = co.height();
        let lt = p3_util::log2_strict_usize(t);
        let mut blocks: Vec<usize> = ranges
            .iter()
            .filter(|r| r.1 <= t)
            .map(|r| r.0 / t)
            .collect();
        blocks.sort_unstable();
        blocks.dedup();
        // (measured: 1.7-2.6x faster openings for T <= 2^13, where the block
        // DFTs stay in cache; 3x slower at T = 2^16 with AVX-512 folds)
        let by_block = lt <= 13
            && ranges.iter().all(|r| r.1 <= t)
            && blocks.len() * (lt / 2 + 2) < ranges.len();
        if by_block {
            for &b in &blocks {
                let ev = crate::lowmem::eval_range(dft, &co, m.lde, m.shift, b * t, t, None);
                for (i, &(p0, len)) in ranges.iter().enumerate() {
                    if p0 / t == b {
                        let u = p0 - b * t;
                        evs[i] = Some(RowMajorMatrix::new(
                            ev.values[u * cw..(u + len) * cw].to_vec(),
                            cw,
                        ));
                    }
                }
            }
        }
        for &l in lens.iter().filter(|_| !by_block) {
            let idx: Vec<usize> = (0..ranges.len()).filter(|&i| ranges[i].1 == l).collect();
            let p0s: Vec<usize> = idx.iter().map(|&i| ranges[i].0).collect();
            for (i, e) in idx.iter().zip(crate::lowmem::eval_ranges(
                dft, &co, m.lde, m.shift, &p0s, l,
            )) {
                evs[*i] = Some(e);
            }
        }
        let mut off = 0;
        for (e, &(_, len)) in evs.iter().zip(ranges) {
            let e = e.as_ref().unwrap();
            for i in 0..len {
                out[off + i][c0..c1].copy_from_slice(&e.values[i * cw..(i + 1) * cw]);
            }
            off += len;
        }
    }
    out
}

/// Open a round at level-0 query positions (same multiproof as
/// [`crate::mmcs::open`]).
pub fn open(dft: &Dft, mats: &[CMat], tree: &LTree, queries: &[usize], chunk: usize) -> Opening {
    let l0 = tree.l0;
    let keep = (0..=l0).find(|&k| tree.levels[k].is_some()).unwrap();
    let sets = index_sets(l0, queries);
    let gsz = 1usize << keep;
    // 2^keep-aligned groups of level-0 positions
    let mut groups: Vec<usize> = queries.iter().map(|&q| q / gsz).collect();
    groups.sort_unstable();
    groups.dedup();
    // rows of each matrix on its level's part of every group (or, for
    // classes ≥ keep, at the opened positions themselves)
    let mut rowmap: Vec<HashMap<usize, Vec<F>>> = vec![];
    for m in mats {
        let k = m.class;
        let ranges: Vec<(usize, usize)> = if k < keep {
            groups.iter().map(|&g| ((g * gsz) >> k, gsz >> k)).collect()
        } else {
            sets[k].iter().map(|&j| (j, 1)).collect()
        };
        let rows = rows_on(dft, m, &ranges, chunk);
        let mut map = HashMap::new();
        let mut i = 0;
        for &(p0, len) in &ranges {
            for u in 0..len {
                map.insert(p0 + u, rows[i].clone());
                i += 1;
            }
        }
        rowmap.push(map);
    }
    let row_bytes = |k: usize, j: usize| -> Vec<u8> {
        let mut b = vec![];
        for (m, map) in mats.iter().zip(&rowmap) {
            if m.class == k {
                for x in &map[&j] {
                    b.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
                }
            }
        }
        b
    };
    // recompute levels < keep inside the groups
    // (groups are independent subtrees: hashed in parallel)
    use rayon::prelude::*;
    let parts: Vec<Vec<((usize, usize), Digest64)>> = groups
        .par_iter()
        .map(|&g| {
            let mut loc: HashMap<(usize, usize), Digest64> = HashMap::new();
            for j in g * gsz..(g + 1) * gsz {
                loc.insert((0, j), wh(TAG_LEAF, &[&row_bytes(0, j)]));
            }
            for k in 1..keep {
                for j in (g * gsz) >> k..((g + 1) * gsz) >> k {
                    let (a, b) = (loc[&(k - 1, 2 * j)], loc[&(k - 1, 2 * j + 1)]);
                    loc.insert(
                        (k, j),
                        wh(TAG_NODE, &[&[k as u8], &a, &b, &row_bytes(k, j)]),
                    );
                }
            }
            loc.into_iter().collect()
        })
        .collect();
    let low: HashMap<(usize, usize), Digest64> = parts.into_iter().flatten().collect();
    let node = |k: usize, j: usize| -> Digest64 {
        match &tree.levels[k] {
            Some(l) => l[j],
            None => low[&(k, j)],
        }
    };
    let rows = mats
        .iter()
        .zip(&rowmap)
        .map(|(m, map)| {
            let mut r = vec![];
            for &j in &sets[m.class] {
                r.extend_from_slice(&map[&j]);
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
                    siblings.push(node(k - 1, c));
                }
            }
        }
    }
    Opening { rows, siblings }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cols::TraceCols;
    use crate::field::{F, shift};
    use crate::mmcs::{self, Mat};
    use p3_dft::TwoAdicSubgroupDft;
    use p3_field::PrimeCharacteristicRing;

    #[test]
    fn matches_mmcs() {
        let dft = Dft::default();
        // tables: 2^9 rows w=5 (class 0), 2^7 rows w=3 (class 2), 2^9 rows w=0
        let mk = |lh: usize, w: usize, seed: u32| {
            TraceCols::from_rows(lh, w, |r, b| {
                for c in 0..w {
                    b[c] = (r as u32 * 7 + c as u32 * 13 + seed).wrapping_mul(2654435761u32)
                        % 2013265921;
                }
            })
        };
        let ts = [mk(9, 5, 1), mk(7, 3, 2), mk(9, 0, 0)];
        let l0 = 13;
        let srcs: Vec<Src> = ts.iter().map(Src::Main).collect();
        let mats: Vec<CMat> = srcs
            .iter()
            .zip(&ts)
            .map(|(s, t)| {
                let class = l0 - (t.log_h + 4);
                CMat {
                    src: s,
                    lde: t.log_h + 4,
                    shift: shift().exp_power_of_2(class),
                    class,
                }
            })
            .collect();
        // reference: full LDE (natural) as bitrev Mats
        let refm: Vec<Mat> = ts
            .iter()
            .zip(&mats)
            .map(|(t, m)| {
                let v = if t.width() == 0 {
                    vec![]
                } else {
                    dft.coset_lde_batch(t.chunk(0, t.width()), 4, m.shift)
                        .to_row_major_matrix()
                        .values
                };
                Mat {
                    width: t.width(),
                    log_height: m.lde,
                    values: v,
                    bitrev: true,
                }
            })
            .collect();
        let rt = mmcs::commit(&refm);
        for (group, chunk) in [(1 << 13, 64), (1 << 11, 2), (1 << 12, 8)] {
            let t = commit(&dft, &mats, l0, group, chunk, KEEP);
            assert_eq!(t.root(), rt.root());
            let qs = vec![5, 8000, 4097, 5, 123];
            let a = open(&dft, &mats, &t, &qs, chunk);
            let b = mmcs::open(&refm, &rt, &qs);
            assert_eq!(a, b);
        }
        let _ = F::ZERO;
    }
}
