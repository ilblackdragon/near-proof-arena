//! SHA table: one SHA-256 compression per row, plus message framing.
//!
//! Columns = Plonky3's `Sha256Cols` (bit-level compression) followed by:
//! `act, first, last, msg, blk, cnt, seen, p80, pn, dm, f[64]`.
//!
//! * `f[k]` = 1 iff byte `k` of this block is message data (monotone).
//!   Data bytes are *received* on `BUS_BYTES` as `(msg, 64*blk + k, byte_k)`
//!   where `byte_k` is read from the block's bit columns, so every byte a
//!   producer emits is range-checked here.
//! * Padding (FIPS 180-4 §5.1.1) is enforced locally: the `0x80` byte sits
//!   right after the data (`p80` marks the block that holds it, `seen` that a
//!   previous block did), all other non-data bytes are zero, and the last
//!   block ends with the 64-bit big-endian bit length `8 * (cnt + d)`. The
//!   rules force the minimal (standard) padding.
//! * Blocks of one message are chained through `BUS_CHAIN`
//!   `(msg, blk, cnt, seen, h[16])` instead of next-row access, so rows are
//!   independent and the table opens at a single out-of-domain point.
//! * The last block provides the digest on `BUS_DIGEST` as 16 big-endian
//!   16-bit limbs, with free multiplicity `dm`.
//!
//! No row ever reads its neighbour; max constraint degree is 3.

use super::sha_core::eval_sha_row;
use super::*;
use crate::consts::*;
use p3_sha256_air::{NUM_SHA256_COLS, SHA256_IV, Sha256Cols};
use std::borrow::Borrow;

#[derive(Clone, Debug)]
pub struct ShaCols {
    pub act: usize,
    pub first: usize,
    pub last: usize,
    pub msg: usize,
    pub blk: usize,
    pub cnt: usize,
    pub seen: usize,
    pub p80: usize,
    pub pn: usize,
    pub dm: usize,
    pub f: [usize; 64],
    pub width: usize,
}

impl ShaCols {
    pub fn new() -> Self {
        let mut a = Alloc(NUM_SHA256_COLS);
        let c = ShaCols {
            act: a.one(),
            first: a.one(),
            last: a.one(),
            msg: a.one(),
            blk: a.one(),
            cnt: a.one(),
            seen: a.one(),
            p80: a.one(),
            pn: a.one(),
            dm: a.one(),
            f: a.arr(),
            width: 0,
        };
        ShaCols { width: a.0, ..c }
    }
}

/// Column index of bit `t` (LSB = 0) of message-schedule word `w`.
pub fn w_bit_col(w: usize, t: usize) -> usize {
    // Sha256Cols layout: h_in [8][2], a_chain [68][32], e_chain [68][32], w [64][32], ...
    2 * 8 + 68 * 32 * 2 + w * 32 + t
}

#[derive(Clone, Debug)]
pub struct ShaAir {
    pub c: ShaCols,
}

impl ShaAir {
    pub fn new() -> Self {
        ShaAir { c: ShaCols::new() }
    }
    pub fn width(&self) -> usize {
        self.c.width
    }

    pub fn eval<AB: AirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        let c = &self.c;
        let r = Rows::<AB>::new(b, false);
        {
            let sha: &Sha256Cols<AB::Var> = r.cur[..NUM_SHA256_COLS].borrow();
            eval_sha_row(b, sha);
        }
        let sha: &Sha256Cols<AB::Var> = r.cur[..NUM_SHA256_COLS].borrow();
        let v = |i: usize| r.c(i);
        let one = AB::Expr::ONE;
        let (act, first, last, seen, p80, pn) =
            (v(c.act), v(c.first), v(c.last), v(c.seen), v(c.p80), v(c.pn));
        let f: Vec<AB::Expr> = c.f.iter().map(|&i| v(i)).collect();

        for x in [&act, &first, &last, &seen, &p80] {
            b.assert_bool(x.clone());
        }
        for fk in &f {
            b.assert_bool(fk.clone());
        }
        // Inactive rows: no flags, no data, no digest.
        b.assert_zero((one.clone() - act.clone()) * first.clone());
        b.assert_zero((one.clone() - act.clone()) * last.clone());
        b.assert_zero((one.clone() - act.clone()) * p80.clone());
        b.assert_zero((one.clone() - act.clone()) * seen.clone());
        b.assert_zero((one.clone() - act.clone()) * f[0].clone());
        b.assert_zero((one.clone() - last.clone()) * v(c.dm));
        // pn = p80 * (1 - last)
        b.assert_eq(pn.clone(), p80.clone() * (one.clone() - last.clone()));
        // Monotone data flags.
        for k in 0..63 {
            b.assert_zero(f[k + 1].clone() * (one.clone() - f[k].clone()));
        }
        // First block: non-empty message, fresh state.
        b.assert_zero(first.clone() * (one.clone() - f[0].clone()));
        b.assert_zero(first.clone() * v(c.blk));
        b.assert_zero(first.clone() * v(c.cnt));
        b.assert_zero(first.clone() * seen.clone());
        for i in 0..8 {
            let iv = SHA256_IV[i];
            b.assert_zero(first.clone() * (sha.h_in[i][0].into() - k::<AB>((iv & 0xffff) as u64)));
            b.assert_zero(first.clone() * (sha.h_in[i][1].into() - k::<AB>((iv >> 16) as u64)));
        }

        // Block bytes from the schedule bits (word w big-endian).
        let byte = |kk: usize| -> AB::Expr {
            let w = kk / 4;
            let base = 8 * (3 - kk % 4);
            let mut acc = AB::Expr::ZERO;
            for t in (0..8).rev() {
                acc = acc * AB::Expr::TWO + v(w_bit_col(w, base + t));
            }
            acc
        };
        let bytes: Vec<AB::Expr> = (0..64).map(byte).collect();
        let e = |kk: usize| -> AB::Expr {
            if kk == 0 { one.clone() - f[0].clone() } else { f[kk - 1].clone() - f[kk].clone() }
        };
        // Non-data bytes: 0x80 right after the data, else zero; in the last
        // block bytes 56..64 hold the length instead.
        for kk in 0..64 {
            if kk < 56 {
                b.assert_zero(
                    (one.clone() - f[kk].clone())
                        * (bytes[kk].clone() - k::<AB>(128) * p80.clone() * e(kk)),
                );
            } else {
                b.assert_zero(
                    (one.clone() - f[kk].clone())
                        * ((one.clone() - last.clone()) * bytes[kk].clone()
                            - k::<AB>(128) * pn.clone() * e(kk)),
                );
            }
        }
        // 0x80 rules.
        b.assert_zero(p80.clone() * f[63].clone());
        b.assert_zero(seen.clone() * p80.clone());
        b.assert_zero((act.clone() - f[63].clone()) * (one.clone() - seen.clone() - p80.clone()));
        b.assert_zero(seen.clone() * f[0].clone());
        b.assert_zero(seen.clone() * (one.clone() - last.clone()));
        b.assert_zero((one.clone() - last.clone()) * p80.clone() * (one.clone() - f[55].clone()));
        b.assert_zero(last.clone() * (one.clone() - seen.clone() - p80.clone()));
        b.assert_zero(last.clone() * f[56].clone());
        b.assert_zero(last.clone() * p80.clone() * e(56));
        // Length: word 14 = 0, word 15 = 8 * (cnt + d) with bits 28..32 zero.
        let d = f.iter().fold(AB::Expr::ZERO, |a, x| a + x.clone());
        let mut w14 = AB::Expr::ZERO;
        for t in 0..32 {
            w14 = w14 + v(w_bit_col(14, t));
        }
        b.assert_zero(last.clone() * w14);
        for t in 28..32 {
            b.assert_zero(last.clone() * v(w_bit_col(15, t)));
        }
        let mut w15 = AB::Expr::ZERO;
        for t in (0..28).rev() {
            w15 = w15 * AB::Expr::TWO + v(w_bit_col(15, t));
        }
        b.assert_zero(last.clone() * (w15 - k::<AB>(8) * (v(c.cnt) + d.clone())));

        // Chaining.
        let h_out_limbs = |i: usize| -> [AB::Expr; 2] {
            let mut lo = AB::Expr::ZERO;
            let mut hi = AB::Expr::ZERO;
            for t in (0..16).rev() {
                lo = lo * AB::Expr::TWO + sha.h_out[i][t].into();
                hi = hi * AB::Expr::TWO + sha.h_out[i][16 + t].into();
            }
            [lo, hi]
        };
        let mut out_tuple = vec![
            v(c.msg),
            v(c.blk) + one.clone(),
            v(c.cnt) + d.clone(),
            seen.clone() + p80.clone(),
        ];
        let mut in_tuple = vec![v(c.msg), v(c.blk), v(c.cnt), seen.clone()];
        let mut digest = vec![v(c.msg)];
        for i in 0..8 {
            let [lo, hi] = h_out_limbs(i);
            out_tuple.push(lo.clone());
            out_tuple.push(hi.clone());
            in_tuple.push(sha.h_in[i][0].into());
            in_tuple.push(sha.h_in[i][1].into());
            digest.push(hi);
            digest.push(lo);
        }
        send(b, BUS_CHAIN, out_tuple, act.clone() * (one.clone() - last.clone()));
        recv(b, BUS_CHAIN, in_tuple, act.clone() * (one.clone() - first.clone()));
        provide(b, BUS_DIGEST, digest, v(c.dm));
        // Data bytes.
        let base = v(c.blk) * k::<AB>(64);
        for kk in 0..64 {
            recv(
                b,
                BUS_BYTES,
                vec![v(c.msg), base.clone() + k::<AB>(kk as u64), bytes[kk].clone()],
                f[kk].clone(),
            );
        }
    }
}
