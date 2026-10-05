//! Building blocks of the low-memory prover.
//!
//! * [`eval_range`]: evaluations of column polynomials (given by their
//!   coefficients) on an aligned range of bit-reversed LDE positions. A range
//!   of `m = 2^a ≤ T` positions starting at `p0` (a multiple of `m`) is the
//!   coset `c·⟨ω_m⟩` (in bit-reversed order) with
//!   `c = s_t · ω_l^{bitrev_{l-a}(p0 >> a)}`; it is computed by folding the
//!   coefficients modulo `X^m − c^m` and one size-`m` coset DFT. Ranges larger
//!   than `T` are unions of such blocks.
//! * [`WhStream`]: the wide hash `WH(tag, prefix ‖ body)` of many messages that
//!   share their layout, fed in column chunks (one SHA-256 state pair and a
//!   carry buffer per message), so a Merkle level can be hashed without ever
//!   holding all columns of a row.

use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::{Field, PackedValue, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use rayon::prelude::*;
use sha2::digest::generic_array::GenericArray;

use crate::field::{omega, F};
use crate::hash::{Digest64, RO_TAG};
use crate::mmcs::rev;

pub type Dft = Radix2DitParallel<F>;

/// Bit-reverse the rows of a row-major matrix in place.
pub fn reverse_rows(m: &mut RowMajorMatrix<F>) {
    let w = m.width();
    let h = m.height();
    if w == 0 || h <= 2 {
        return;
    }
    let bits = p3_util::log2_strict_usize(h);
    for i in 0..h {
        let j = rev(i, bits);
        if i < j {
            let (a, b) = m.values.split_at_mut(j * w);
            a[i * w..(i + 1) * w].swap_with_slice(&mut b[..w]);
        }
    }
}

/// `Σ_j f[j·m + i] · y^j` for `i < m` (rows of `f`, `C` columns).
fn fold(f: &RowMajorMatrix<F>, m: usize, y: F) -> RowMajorMatrix<F> {
    type P = <F as Field>::Packing;
    let w = f.width();
    let t = f.height();
    let k = t / m;
    if k == 1 {
        return f.clone();
    }
    let ys: Vec<F> = y.powers().take(k).collect();
    let mut out = vec![F::ZERO; m * w];
    let lanes = P::WIDTH;
    let full = w / lanes;
    out.par_chunks_mut(w * 64.min(m)).enumerate().for_each(|(ci, o)| {
        let i0 = ci * 64.min(m);
        for (di, orow) in o.chunks_mut(w).enumerate() {
            let i = i0 + di;
            let (op, ot) = orow.split_at_mut(full * lanes);
            let opk = P::pack_slice_mut(op);
            for j in 0..k {
                let src = &f.values[(j * m + i) * w..(j * m + i + 1) * w];
                let yj = ys[j];
                let pj = P::from(yj);
                let (sp, st) = src.split_at(full * lanes);
                for (a, b) in opk.iter_mut().zip(P::pack_slice(sp)) {
                    *a += pj * *b;
                }
                for (a, b) in ot.iter_mut().zip(st) {
                    *a += yj * *b;
                }
            }
        }
    });
    RowMajorMatrix::new(out, w)
}

/// Evaluations, in bit-reversed position order, of the polynomials with
/// coefficients `coeffs` (`T × C`) at positions `p0 .. p0+len` of the LDE of
/// log size `l` and coset shift `shift`; with `twist = Some(g)` the
/// polynomials `f(g·X)` instead (next-row values). `len` is a power of two
/// and `p0` a multiple of `len`.
pub fn eval_range(
    dft: &Dft,
    coeffs: &RowMajorMatrix<F>,
    l: usize,
    shift: F,
    p0: usize,
    len: usize,
    twist: Option<F>,
) -> RowMajorMatrix<F> {
    let t = coeffs.height();
    let w = coeffs.width();
    if len > t {
        let mut out = Vec::with_capacity(len * w);
        for b in 0..len / t {
            out.extend(eval_range(dft, coeffs, l, shift, p0 + b * t, t, twist).values);
        }
        return RowMajorMatrix::new(out, w);
    }
    let a = p3_util::log2_strict_usize(len);
    let kk = p0 >> a;
    let mut c = shift * omega(l).exp_u64(rev(kk, l - a) as u64);
    if let Some(g) = twist {
        c *= g;
    }
    if w == 0 {
        return RowMajorMatrix::new(vec![], 0);
    }
    if len == 1 {
        // single point: Horner
        let mut v = vec![F::ZERO; w];
        for i in (0..t).rev() {
            let row = &coeffs.values[i * w..(i + 1) * w];
            for (x, r) in v.iter_mut().zip(row) {
                *x = *x * c + *r;
            }
        }
        return RowMajorMatrix::new(v, w);
    }
    let h = fold(coeffs, len, c.exp_u64(len as u64));
    let mut e = dft.coset_dft_batch(h, c).to_row_major_matrix();
    reverse_rows(&mut e);
    e
}

// ---------------------------------------------------------------------------
// Streaming wide hash
// ---------------------------------------------------------------------------

const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// `n` messages `m_i = tag ‖ v ‖ body_i` hashed as `WH(tag, body_i)` =
/// `H(tag‖1‖body) ‖ H(tag‖2‖body)` (`H(x) = SHA-256("NPAI-RO-v1" ‖ x)`), all
/// bodies fed in lock step with equal lengths.
pub struct WhStream {
    n: usize,
    /// two states per message
    st: Vec<[u32; 16]>,
    /// carry buffer per message (64 bytes)
    buf: Vec<[u8; 64]>,
    /// bytes in each buffer (common to all messages)
    carry: usize,
    /// total message bytes so far (including `RO_TAG`)
    total: u64,
    /// whether block 0 (which holds the variant byte) has been compressed
    first_done: bool,
}

#[inline]
fn compress(st: &mut [u32], block: &[u8; 64]) {
    let s: &mut [u32; 8] = st.try_into().unwrap();
    sha2::compress256(s, &[*GenericArray::from_slice(block)]);
}

impl WhStream {
    pub fn new(n: usize, tag: u8) -> WhStream {
        let mut b0 = [0u8; 64];
        b0[..10].copy_from_slice(RO_TAG);
        b0[10] = tag;
        // b0[11] = variant, set when block 0 is compressed
        let mut st = [0u32; 16];
        st[..8].copy_from_slice(&H0);
        st[8..].copy_from_slice(&H0);
        WhStream { n, st: vec![st; n], buf: vec![b0; n], carry: 12, total: 12, first_done: false }
    }

    pub fn len(&self) -> usize {
        self.n
    }

    fn absorb_one(st: &mut [u32; 16], buf: &mut [u8; 64], first_done: bool, mut carry: usize, bytes: &[u8]) {
        let mut first = first_done;
        let mut off = 0;
        while off < bytes.len() {
            let take = (64 - carry).min(bytes.len() - off);
            buf[carry..carry + take].copy_from_slice(&bytes[off..off + take]);
            carry += take;
            off += take;
            if carry == 64 {
                if first {
                    compress(&mut st[..8], buf);
                    compress(&mut st[8..], buf);
                } else {
                    buf[11] = 1;
                    compress(&mut st[..8], buf);
                    buf[11] = 2;
                    compress(&mut st[8..], buf);
                    first = true;
                }
                carry = 0;
            }
        }
    }

    fn advance(&mut self, len: usize) {
        let nf = self.first_done || self.carry + len >= 64;
        self.carry = (self.carry + len) % 64;
        self.total += len as u64;
        self.first_done = nf;
    }

    /// Append `body(i, out)` (exactly `len` bytes) to every message `i`.
    pub fn feed(&mut self, len: usize, body: impl Fn(usize, &mut Vec<u8>) + Sync) {
        let (fd, carry) = (self.first_done, self.carry);
        self.st.par_iter_mut().zip(self.buf.par_iter_mut()).enumerate().for_each_init(
            || Vec::with_capacity(len),
            |tmp, (i, (st, buf))| {
                tmp.clear();
                body(i, tmp);
                debug_assert_eq!(tmp.len(), len);
                Self::absorb_one(st, buf, fd, carry, tmp);
            },
        );
        self.advance(len);
    }

    /// Append row `i` of `rows` (`n × w` field elements, u32 LE) to message `i`.
    pub fn feed_rows(&mut self, rows: &RowMajorMatrix<F>) {
        let w = rows.width();
        assert_eq!(rows.height(), self.n);
        self.feed(4 * w, |i, out| {
            for x in &rows.values[i * w..(i + 1) * w] {
                out.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
            }
        });
    }

    pub fn finish(self) -> Vec<Digest64> {
        let (fd, carry, total) = (self.first_done, self.carry, self.total);
        self.st
            .into_par_iter()
            .zip(self.buf.into_par_iter())
            .map(|(mut st, mut buf)| {
                let mut first = fd;
                let mut c = carry;
                let bits = total * 8;
                buf[c] = 0x80;
                c += 1;
                let mut blocks: Vec<[u8; 64]> = vec![];
                if c > 56 {
                    buf[c..].fill(0);
                    blocks.push(buf);
                    buf = [0u8; 64];
                    c = 0;
                }
                buf[c..56].fill(0);
                buf[56..].copy_from_slice(&bits.to_be_bytes());
                blocks.push(buf);
                for mut b in blocks {
                    if first {
                        compress(&mut st[..8], &b);
                        compress(&mut st[8..], &b);
                    } else {
                        b[11] = 1;
                        compress(&mut st[..8], &b);
                        b[11] = 2;
                        compress(&mut st[8..], &b);
                        first = true;
                    }
                }
                let mut out = [0u8; 64];
                for (k, w) in st.iter().enumerate() {
                    out[4 * k..4 * k + 4].copy_from_slice(&w.to_be_bytes());
                }
                out
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::wh;

    #[test]
    fn wh_stream_matches() {
        for lens in [vec![0usize], vec![3], vec![52], vec![53], vec![51, 7], vec![10, 64, 100, 1], vec![200, 3, 4]] {
            let n = 5;
            let mut s = WhStream::new(n, 7);
            let mut msgs = vec![vec![]; n];
            for (k, &l) in lens.iter().enumerate() {
                let body = |i: usize, out: &mut Vec<u8>| {
                    for j in 0..l {
                        out.push((i * 31 + j * 7 + k) as u8);
                    }
                };
                for (i, m) in msgs.iter_mut().enumerate() {
                    body(i, m);
                }
                s.feed(l, body);
            }
            let got = s.finish();
            for i in 0..n {
                assert_eq!(got[i], wh(7, &[&msgs[i]]), "lens {lens:?} msg {i}");
            }
        }
    }

    #[test]
    fn eval_range_matches_full_lde() {
        use crate::field::shift;
        let dft = Dft::default();
        let h = 5;
        let t = 1 << h;
        let w = 3;
        let vals: Vec<F> = (0..(t * w) as u32).map(|i| F::new(i * 7919 % 1000003)).collect();
        let coeffs = dft.idft_batch(RowMajorMatrix::new(vals, w));
        let l = h + 4;
        let sh = shift().exp_power_of_2(1);
        // reference: evaluate at every position directly
        let g = omega(h);
        for (p0, len) in [(0usize, 16 * t), (t, t), (3 * t, t), (40, 8), (16, 16), (7, 1), (64, 64)] {
            for twist in [None, Some(g)] {
                let e = eval_range(&dft, &coeffs, l, sh, p0, len, twist);
                for u in 0..len {
                    let p = p0 + u;
                    let mut x = sh * omega(l).exp_u64(rev(p, l) as u64);
                    if let Some(g) = twist {
                        x *= g;
                    }
                    for c in 0..w {
                        let mut acc = F::ZERO;
                        for i in (0..t).rev() {
                            acc = acc * x + coeffs.values[i * w + c];
                        }
                        assert_eq!(e.values[u * w + c], acc, "p0 {p0} len {len} u {u} c {c}");
                    }
                }
            }
        }
    }
}
