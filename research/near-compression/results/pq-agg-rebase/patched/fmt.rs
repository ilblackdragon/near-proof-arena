//! NV word format: 64-bit SHA words as the air2 compression AIR's three limbs
//! (split at 21/42 bits for digit width k = 3, at 22/44 bits for k <= 2).
//! A SHA-384 digest is 6 words = 18 limbs (H0 limb 0 first).
use std::sync::OnceLock;

use p3_field::{PrimeCharacteristicRing, PrimeField32};

use crate::sha384::config::{digest_from_words, digest_words, Digest, F};

pub const NV_DIGEST: usize = 18;

/// Digit width of the SHA AIR (env NEARPROOF_SHA_K, default 3).
pub fn sha_k() -> usize {
    static K: OnceLock<usize> = OnceLock::new();
    *K.get_or_init(|| {
        std::env::var("NEARPROOF_SHA_K")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(3)
    })
}

/// Limb boundaries (bits).
pub fn limb_off() -> [usize; 4] {
    if sha_k() == 3 {
        [0, 21, 42, 64]
    } else {
        [0, 22, 44, 64]
    }
}

pub fn wl(w: u64) -> [u32; 3] {
    let o = limb_off();
    std::array::from_fn(|i| ((w >> o[i]) & ((1u64 << (o[i + 1] - o[i])) - 1)) as u32)
}
pub fn lw(l: &[u32]) -> u64 {
    let o = limb_off();
    (0..3).fold(0u64, |a, i| a | ((l[i] as u64) << o[i]))
}
pub fn digest_limbs(d: Digest) -> [F; NV_DIGEST] {
    let h = digest_words(d);
    std::array::from_fn(|i| F::from_u32(wl(h[i / 3])[i % 3]))
}
pub fn limbs_digest(l: &[F]) -> Digest {
    let u: Vec<u32> = l.iter().map(|x| x.as_canonical_u32()).collect();
    digest_from_words(std::array::from_fn(|i| lw(&u[3 * i..3 * i + 3])))
}

/// Byte split points for the limbs of a big-endian word (b0 = MSB): byte 5 is split at
/// `s5` low bits, byte 2 at `s2` low bits.
pub fn split_bits() -> (usize, usize) {
    if sha_k() == 3 {
        (5, 2)
    } else {
        (6, 4)
    }
}

/// Limbs of a word given as big-endian bytes and the low parts of bytes 5 and 2.
pub fn limbs_from_bytes<E: PrimeCharacteristicRing + Clone>(b: &[E; 8], lo5: E, lo2: E) -> [E; 3] {
    let (a5, a2) = split_bits();
    let c = |v: u64| E::from_u64(v);
    let o = limb_off();
    // bits: b7 = 0..7, b6 = 8..15, b5 = 16..23, b4 = 24..31, b3 = 32..39, b2 = 40..47, b1, b0
    let inv = |a: usize| E::from_u32(p3_field::Field::inverse(&F::from_u64(1 << a)).as_canonical_u32());
    let hi5 = (b[5].clone() - lo5.clone()) * inv(a5);
    let hi2 = (b[2].clone() - lo2.clone()) * inv(a2);
    let l0 = b[7].clone() + b[6].clone() * c(1 << 8) + lo5 * c(1 << 16);
    let s1 = 16 + a5 - o[1]; // 0
    debug_assert_eq!(s1, 0);
    let l1 = hi5
        + b[4].clone() * c(1 << (24 - o[1]))
        + b[3].clone() * c(1 << (32 - o[1]))
        + lo2 * c(1 << (40 - o[1]));
    let l2 = hi2 + b[1].clone() * c(1 << (48 - o[2])) + b[0].clone() * c(1 << (56 - o[2]));
    [l0, l1, l2]
}

/// Constant word as limbs.
pub fn const_limbs<E: PrimeCharacteristicRing>(w: u64) -> [E; 3] {
    wl(w).map(|x| E::from_u32(x))
}
