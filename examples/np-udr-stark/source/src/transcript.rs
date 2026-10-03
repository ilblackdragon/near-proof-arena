//! Full-prefix Fiat–Shamir transcript through the 512-bit hash chain.
//!
//! * `d_0 = WH(INIT, "np-udr-stark-v1" ‖ le64(|pub|) ‖ pub ‖ le64(|cb|) ‖ cb)`
//!   (`pub` = the full public tape); the proof header is part of message 0.
//! * every challenge is preceded by exactly one absorbed message `m`
//!   (possibly empty): `d ← WH(ABS, d ‖ m)`, then
//!   `c = decodeChal(H(CHAL ‖ d))` (or `decodeOod` for the OOD point).
//! * after the last message (the final FRI polynomial), `d_fin ← WH(ABS, d ‖ m)`,
//!   and query chunk `j < 24` is `H(QUERY ‖ d_fin ‖ u8(j))`.
//! * a query chunk `A` (32 bytes) read as a big-endian 256-bit integer `N`
//!   yields positions `(N >> 26·i) mod 2^26 mod n0` for `i = 0..9`.

use crate::field::{decode_chal, decode_ood, EF};
use crate::hash::{h, wh, Digest32, Digest64, TAG_ABS, TAG_CHAL, TAG_INIT, TAG_QUERY};

pub const PROTOCOL_ID: &[u8] = b"np-udr-stark-v1";

pub struct Transcript {
    pub d: Digest64,
    pending: Option<Vec<u8>>,
}

impl Transcript {
    pub fn new(pub_tape: &[u8], cb: &[u8]) -> Self {
        let d = wh(
            TAG_INIT,
            &[PROTOCOL_ID, &(pub_tape.len() as u64).to_le_bytes(), pub_tape, &(cb.len() as u64).to_le_bytes(), cb],
        );
        Transcript { d, pending: None }
    }

    /// Queue the prover message preceding the next challenge.
    pub fn absorb(&mut self, msg: Vec<u8>) {
        assert!(self.pending.is_none(), "two messages without a challenge");
        self.pending = Some(msg);
    }

    fn step(&mut self) {
        let m = self.pending.take().unwrap_or_default();
        self.d = wh(TAG_ABS, &[&self.d, &m]);
    }

    fn raw(&mut self) -> Digest32 {
        self.step();
        h(&[&[TAG_CHAL], &self.d])
    }

    pub fn chal(&mut self) -> EF {
        let y = self.raw();
        decode_chal(&y)
    }

    pub fn chal_ood(&mut self) -> EF {
        let y = self.raw();
        decode_ood(&y)
    }

    /// Absorb the final message and derive the query positions in `[0, n0)`.
    pub fn finish_queries(&mut self, log_n0: usize, chunks: usize, per_chunk: usize) -> Vec<usize> {
        self.step();
        let mut out = Vec::with_capacity(chunks * per_chunk);
        for j in 0..chunks {
            let a = h(&[&[TAG_QUERY], &self.d, &[j as u8]]);
            out.extend(positions(&a, per_chunk).into_iter().map(|p| p & ((1 << log_n0) - 1)));
        }
        out
    }
}

/// `(N >> 26·i) mod 2^26` for `i < k`, `N` the big-endian integer of `a`.
pub fn positions(a: &Digest32, k: usize) -> Vec<usize> {
    (0..k)
        .map(|i| {
            let mut v = 0usize;
            for b in 0..26 {
                let bit = 26 * i + b; // bit index from the least significant end
                let byte = a[31 - bit / 8];
                if (byte >> (bit % 8)) & 1 == 1 {
                    v |= 1 << b;
                }
            }
            v
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn positions_low_bits() {
        let mut a = [0u8; 32];
        a[31] = 0x05; // N = 5
        a[28] = 0x04; // bit 26 set -> position 1 = 1
        let p = positions(&a, 9);
        assert_eq!(p[0], 5);
        assert_eq!(p[1], 1);
        assert!(p[2..].iter().all(|&x| x == 0));
    }
}
