//! Compact column-major trace storage.
//!
//! The worst in-domain NEAR witness yields tables of `2^22` rows × hundreds
//! of columns; as `F` (4 bytes) the SHA table alone would take 9 GB. Most
//! columns hold bits, bytes or small counters, so each column is stored with
//! the narrowest of `u8`/`u16`/`u32` that fits its maximal value.
//!
//! A table is built in two passes over a row generator (`from_rows`): the
//! first pass finds the per-column maxima, the second fills the columns.

use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use rayon::prelude::*;

use crate::field::{F, P};

#[derive(Clone, Debug)]
pub enum Col {
    U8(Vec<u8>),
    U16(Vec<u16>),
    U32(Vec<u32>),
}

impl Col {
    #[inline]
    pub fn get(&self, r: usize) -> u32 {
        match self {
            Col::U8(v) => v[r] as u32,
            Col::U16(v) => v[r] as u32,
            Col::U32(v) => v[r],
        }
    }
    fn with_max(max: u32, h: usize) -> Col {
        if max < 256 {
            Col::U8(vec![0; h])
        } else if max < 65536 {
            Col::U16(vec![0; h])
        } else {
            Col::U32(vec![0; h])
        }
    }
    #[inline]
    pub fn bytes(&self) -> usize {
        match self {
            Col::U8(v) => v.len(),
            Col::U16(v) => 2 * v.len(),
            Col::U32(v) => 4 * v.len(),
        }
    }
}

/// A trace table: `width` columns of `height = 2^log_h` canonical values.
#[derive(Clone, Debug)]
pub struct TraceCols {
    pub log_h: usize,
    pub cols: Vec<Col>,
}

impl TraceCols {
    pub fn height(&self) -> usize {
        1 << self.log_h
    }
    pub fn width(&self) -> usize {
        self.cols.len()
    }
    pub fn bytes(&self) -> usize {
        self.cols.iter().map(Col::bytes).sum()
    }
    #[inline]
    pub fn get(&self, r: usize, c: usize) -> F {
        F::new(self.cols[c].get(r))
    }

    /// Two passes over `row(r, buf)` (`buf` has `width` entries, values `< p`),
    /// rows processed in parallel chunks.
    pub fn from_rows(log_h: usize, width: usize, row: impl Fn(usize, &mut [u32]) + Sync) -> TraceCols {
        let h = 1usize << log_h;
        const CH: usize = 4096;
        let maxes = (0..h.div_ceil(CH))
            .into_par_iter()
            .map(|k| {
                let mut m = vec![0u32; width];
                let mut buf = vec![0u32; width];
                for r in k * CH..((k + 1) * CH).min(h) {
                    buf.iter_mut().for_each(|x| *x = 0);
                    row(r, &mut buf);
                    for (a, b) in m.iter_mut().zip(&buf) {
                        debug_assert!(*b < P);
                        *a = (*a).max(*b);
                    }
                }
                m
            })
            .reduce(|| vec![0u32; width], |a, b| a.iter().zip(&b).map(|(x, y)| (*x).max(*y)).collect());
        let mut cols: Vec<Col> = maxes.iter().map(|&m| Col::with_max(m, h)).collect();
        // fill: chunks of rows in parallel, writing disjoint row ranges
        let ptrs: Vec<ColPtr> = cols.iter_mut().map(ColPtr::of).collect();
        (0..h.div_ceil(CH)).into_par_iter().for_each(|k| {
            let mut buf = vec![0u32; width];
            for r in k * CH..((k + 1) * CH).min(h) {
                buf.iter_mut().for_each(|x| *x = 0);
                row(r, &mut buf);
                for (c, &x) in buf.iter().enumerate() {
                    // SAFETY: rows r are disjoint across tasks; each column
                    // buffer has `h` entries.
                    unsafe { ptrs[c].write(r, x) }
                }
            }
        });
        TraceCols { log_h, cols }
    }

    pub fn from_matrix(m: &RowMajorMatrix<F>) -> TraceCols {
        use p3_field::PrimeField32;
        let w = m.width();
        let log_h = p3_util::log2_strict_usize(m.height());
        TraceCols::from_rows(log_h, w, |r, buf| {
            for c in 0..w {
                buf[c] = m.values[r * w + c].as_canonical_u32();
            }
        })
    }

    /// Columns `c0..c1` as a row-major `T × (c1-c0)` matrix.
    pub fn chunk(&self, c0: usize, c1: usize) -> RowMajorMatrix<F> {
        let w = c1 - c0;
        let h = self.height();
        let mut v = vec![F::ZERO; h * w];
        v.par_chunks_mut(w.max(1) * 1024).enumerate().for_each(|(k, out)| {
            let r0 = k * 1024;
            for (i, row) in out.chunks_mut(w.max(1)).enumerate() {
                for (j, x) in row.iter_mut().enumerate() {
                    *x = F::new(self.cols[c0 + j].get(r0 + i));
                }
            }
        });
        RowMajorMatrix::new(v, w)
    }

    /// Columns `c0..c1` as a row-major matrix, releasing their storage (each
    /// column keeps its width class for [`TraceCols::put_chunk`]).
    pub fn take_chunk(&mut self, c0: usize, c1: usize) -> RowMajorMatrix<F> {
        let m = self.chunk(c0, c1);
        for c in &mut self.cols[c0..c1] {
            *c = match c {
                Col::U8(_) => Col::U8(Vec::new()),
                Col::U16(_) => Col::U16(Vec::new()),
                Col::U32(_) => Col::U32(Vec::new()),
            };
        }
        m
    }

    /// Refill columns `c0..c0+m.width()` (released by `take_chunk`) from
    /// canonical values that fit their width classes.
    pub fn put_chunk(&mut self, c0: usize, m: &RowMajorMatrix<F>) {
        use p3_field::PrimeField32;
        let w = m.width();
        let h = self.height();
        assert_eq!(m.height(), h);
        for c in &mut self.cols[c0..c0 + w] {
            *c = match c {
                Col::U8(_) => Col::U8(vec![0; h]),
                Col::U16(_) => Col::U16(vec![0; h]),
                Col::U32(_) => Col::U32(vec![0; h]),
            };
        }
        let ptrs: Vec<ColPtr> = self.cols[c0..c0 + w].iter_mut().map(ColPtr::of).collect();
        const CH: usize = 4096;
        (0..h.div_ceil(CH)).into_par_iter().for_each(|k| {
            for r in k * CH..((k + 1) * CH).min(h) {
                for (j, p) in ptrs.iter().enumerate() {
                    let x = m.values[r * w + j].as_canonical_u32();
                    assert!(p.fits(x), "put_chunk: value does not fit its column class");
                    // SAFETY: rows r are disjoint across tasks; each column
                    // buffer has `h` entries.
                    unsafe { p.write(r, x) }
                }
            }
        });
    }

    /// One row into `out` (`width` entries).
    pub fn row_into(&self, r: usize, out: &mut [F]) {
        for (c, x) in out.iter_mut().enumerate() {
            *x = F::new(self.cols[c].get(r));
        }
    }
}

#[derive(Clone, Copy)]
struct ColPtr {
    tag: u8,
    p: *mut u8,
}
unsafe impl Send for ColPtr {}
unsafe impl Sync for ColPtr {}
impl ColPtr {
    fn of(c: &mut Col) -> ColPtr {
        match c {
            Col::U8(v) => ColPtr { tag: 0, p: v.as_mut_ptr() },
            Col::U16(v) => ColPtr { tag: 1, p: v.as_mut_ptr() as *mut u8 },
            Col::U32(v) => ColPtr { tag: 2, p: v.as_mut_ptr() as *mut u8 },
        }
    }
    #[inline]
    fn fits(&self, x: u32) -> bool {
        match self.tag {
            0 => x < 256,
            1 => x < 65536,
            _ => true,
        }
    }
    #[inline]
    unsafe fn write(&self, r: usize, x: u32) {
        unsafe {
            match self.tag {
                0 => *self.p.add(r) = x as u8,
                1 => *(self.p as *mut u16).add(r) = x as u16,
                _ => *(self.p as *mut u32).add(r) = x,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let t = TraceCols::from_rows(10, 3, |r, b| {
            b[0] = (r % 2) as u32;
            b[1] = (r * 300) as u32 % 65536;
            b[2] = (r as u32).wrapping_mul(2654435761) % P;
        });
        assert!(matches!(t.cols[0], Col::U8(_)));
        assert!(matches!(t.cols[1], Col::U16(_)));
        assert!(matches!(t.cols[2], Col::U32(_)));
        let m = t.chunk(0, 3);
        for r in 0..1024 {
            assert_eq!(m.values[3 * r + 1], F::new((r * 300) as u32 % 65536));
        }
    }
}
