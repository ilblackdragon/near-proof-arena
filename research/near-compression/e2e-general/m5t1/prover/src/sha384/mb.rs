//! [pq-cpu-prover] Multi-buffer SHA-384: 8 independent messages per AVX-512 register lane
//! (one 64-bit word of each message per zmm lane), in the style of isa-l_crypto's mb_sha512.
//! Zen 5 has no SHA-512 instructions; one 8-lane compression costs about as much as two scalar
//! ones. Output is plain SHA-384 (FIPS 180-4), checked against the `sha2` crate in the tests.
//!
//! Used for independent hashes only (PoW candidates, Merkle leaves and nodes of one level);
//! every digest is the standard SHA-384 of its message, so proofs are byte-identical.

use sha2::{Digest as _, Sha384};

const IV384: [u64; 8] = [
    0xcbbb9d5dc1059ed8,
    0x629a292a367cd507,
    0x9159015a3070dd17,
    0x152fecd8f70e5939,
    0x67332667ffc00b31,
    0x8eb44a8768581511,
    0xdb0c2e0d64f98fa7,
    0x47b5481dbefa4fa4,
];

const K: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc, 0x3956c25bf348b538,
    0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118, 0xd807aa98a3030242, 0x12835b0145706fbe,
    0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2, 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235,
    0xc19bf174cf692694, 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5, 0x983e5152ee66dfab,
    0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725,
    0x06ca6351e003826f, 0x142929670a0e6e70, 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df, 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218,
    0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8, 0x19a4c116b8d2d0c8, 0x1e376c085141ab53,
    0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3, 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b, 0xca273eceea26619c,
    0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x06f067aa72176fba, 0x0a637dc5a2c898a6,
    0x113f9804bef90dae, 0x1b710b35131c471b, 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

/// Whether the 8-lane kernel is compiled in (`-C target-feature=+avx512f` / `target-cpu=native`).
pub const MB_AVAILABLE: bool = cfg!(all(target_arch = "x86_64", target_feature = "avx512f"));

/// Fast path switch (`NEARPROOF_CPU_FAST=0` restores scalar hashing).
pub fn mb_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    MB_AVAILABLE
        && *ON.get_or_init(|| std::env::var("NEARPROOF_CPU_FAST").map(|v| v != "0").unwrap_or(true))
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
mod x8 {
    use core::arch::x86_64::*;

    use super::K;

    #[inline(always)]
    unsafe fn xor3(a: __m512i, b: __m512i, c: __m512i) -> __m512i {
        _mm512_ternarylogic_epi64::<0x96>(a, b, c)
    }

    /// One compression of 8 lanes. `state[i]` holds word i of every lane; `w16[t][l]` is message
    /// word t (already big-endian decoded) of lane l.
    #[inline(always)]
    pub unsafe fn compress(state: &mut [__m512i; 8], w16: &[[u64; 8]; 16]) {
        let mut w = [_mm512_setzero_si512(); 16];
        for t in 0..16 {
            w[t] = _mm512_loadu_si512(w16[t].as_ptr() as *const _);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
        for t in 0..80 {
            let wt = if t < 16 {
                w[t]
            } else {
                let w15 = w[(t + 1) & 15];
                let w2 = w[(t + 14) & 15];
                let s0 = xor3(_mm512_ror_epi64::<1>(w15), _mm512_ror_epi64::<8>(w15), _mm512_srli_epi64::<7>(w15));
                let s1 = xor3(_mm512_ror_epi64::<19>(w2), _mm512_ror_epi64::<61>(w2), _mm512_srli_epi64::<6>(w2));
                let v = _mm512_add_epi64(_mm512_add_epi64(w[t & 15], s0), _mm512_add_epi64(w[(t + 9) & 15], s1));
                w[t & 15] = v;
                v
            };
            let s1 = xor3(_mm512_ror_epi64::<14>(e), _mm512_ror_epi64::<18>(e), _mm512_ror_epi64::<41>(e));
            let ch = _mm512_ternarylogic_epi64::<0xCA>(e, f, g);
            let t1 = _mm512_add_epi64(
                _mm512_add_epi64(h, s1),
                _mm512_add_epi64(_mm512_add_epi64(ch, _mm512_set1_epi64(K[t] as i64)), wt),
            );
            let s0 = xor3(_mm512_ror_epi64::<28>(a), _mm512_ror_epi64::<34>(a), _mm512_ror_epi64::<39>(a));
            let maj = _mm512_ternarylogic_epi64::<0xE8>(a, b, c);
            let t2 = _mm512_add_epi64(s0, maj);
            h = g;
            g = f;
            f = e;
            e = _mm512_add_epi64(d, t1);
            d = c;
            c = b;
            b = a;
            a = _mm512_add_epi64(t1, t2);
        }
        let n = [a, b, c, d, e, f, g, h];
        for i in 0..8 {
            state[i] = _mm512_add_epi64(state[i], n[i]);
        }
    }
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
mod x16 {
    use core::arch::x86_64::*;

    use super::K;

    #[inline(always)]
    unsafe fn xor3(a: __m512i, b: __m512i, c: __m512i) -> __m512i {
        _mm512_ternarylogic_epi64::<0x96>(a, b, c)
    }

    /// `compress2` starting at round `k` from the working state `v0` (rounds 0..k already
    /// applied); `st` holds the chaining value added at the end.
    #[inline(always)]
    pub unsafe fn compress2_from(st: &mut [[__m512i; 8]; 2], v0: [[__m512i; 8]; 2], k: usize, w16: &[[[u64; 8]; 16]; 2]) {
        let mut w = [[_mm512_setzero_si512(); 16]; 2];
        for g in 0..2 {
            for t in 0..16 {
                w[g][t] = _mm512_loadu_si512(w16[g][t].as_ptr() as *const _);
            }
        }
        let mut v = v0;
        for t in k..80 {
            let kt = _mm512_set1_epi64(K[t] as i64);
            for g in 0..2 {
                let wt = if t < 16 {
                    w[g][t]
                } else {
                    let w15 = w[g][(t + 1) & 15];
                    let w2 = w[g][(t + 14) & 15];
                    let s0 = xor3(_mm512_ror_epi64::<1>(w15), _mm512_ror_epi64::<8>(w15), _mm512_srli_epi64::<7>(w15));
                    let s1 = xor3(_mm512_ror_epi64::<19>(w2), _mm512_ror_epi64::<61>(w2), _mm512_srli_epi64::<6>(w2));
                    let x = _mm512_add_epi64(_mm512_add_epi64(w[g][t & 15], s0), _mm512_add_epi64(w[g][(t + 9) & 15], s1));
                    w[g][t & 15] = x;
                    x
                };
                let [a, b, c, d, e, f, gg, h] = v[g];
                let hkw = _mm512_add_epi64(h, _mm512_add_epi64(kt, wt));
                let s1 = xor3(_mm512_ror_epi64::<14>(e), _mm512_ror_epi64::<18>(e), _mm512_ror_epi64::<41>(e));
                let ch = _mm512_ternarylogic_epi64::<0xCA>(e, f, gg);
                let t1 = _mm512_add_epi64(_mm512_add_epi64(hkw, ch), s1);
                let s0 = xor3(_mm512_ror_epi64::<28>(a), _mm512_ror_epi64::<34>(a), _mm512_ror_epi64::<39>(a));
                let maj = _mm512_ternarylogic_epi64::<0xE8>(a, b, c);
                let t2 = _mm512_add_epi64(s0, maj);
                v[g] = [_mm512_add_epi64(t1, t2), a, b, c, _mm512_add_epi64(d, t1), e, f, gg];
            }
        }
        for g in 0..2 {
            for i in 0..8 {
                st[g][i] = _mm512_add_epi64(st[g][i], v[g][i]);
            }
        }
    }

    /// Two independent 8-lane compressions interleaved (the round function is latency-bound).
    #[inline(always)]
    pub unsafe fn compress2(st: &mut [[__m512i; 8]; 2], w16: &[[[u64; 8]; 16]; 2]) {
        let mut w = [[_mm512_setzero_si512(); 16]; 2];
        for g in 0..2 {
            for t in 0..16 {
                w[g][t] = _mm512_loadu_si512(w16[g][t].as_ptr() as *const _);
            }
        }
        let mut v = *st;
        for t in 0..80 {
            let kt = _mm512_set1_epi64(K[t] as i64);
            for g in 0..2 {
                let wt = if t < 16 {
                    w[g][t]
                } else {
                    let w15 = w[g][(t + 1) & 15];
                    let w2 = w[g][(t + 14) & 15];
                    let s0 = xor3(_mm512_ror_epi64::<1>(w15), _mm512_ror_epi64::<8>(w15), _mm512_srli_epi64::<7>(w15));
                    let s1 = xor3(_mm512_ror_epi64::<19>(w2), _mm512_ror_epi64::<61>(w2), _mm512_srli_epi64::<6>(w2));
                    let x = _mm512_add_epi64(_mm512_add_epi64(w[g][t & 15], s0), _mm512_add_epi64(w[g][(t + 9) & 15], s1));
                    w[g][t & 15] = x;
                    x
                };
                let [a, b, c, d, e, f, gg, h] = v[g];
                let hkw = _mm512_add_epi64(h, _mm512_add_epi64(kt, wt));
                let s1 = xor3(_mm512_ror_epi64::<14>(e), _mm512_ror_epi64::<18>(e), _mm512_ror_epi64::<41>(e));
                let ch = _mm512_ternarylogic_epi64::<0xCA>(e, f, gg);
                let t1 = _mm512_add_epi64(_mm512_add_epi64(hkw, ch), s1);
                let s0 = xor3(_mm512_ror_epi64::<28>(a), _mm512_ror_epi64::<34>(a), _mm512_ror_epi64::<39>(a));
                let maj = _mm512_ternarylogic_epi64::<0xE8>(a, b, c);
                let t2 = _mm512_add_epi64(s0, maj);
                v[g] = [_mm512_add_epi64(t1, t2), a, b, c, _mm512_add_epi64(d, t1), e, f, gg];
            }
        }
        for g in 0..2 {
            for i in 0..8 {
                st[g][i] = _mm512_add_epi64(st[g][i], v[g][i]);
            }
        }
    }
}

/// Scalar SHA-512 state after the first `k` rounds of the compression of `block` from the
/// SHA-384 IV (for PoW candidates that agree on message words 0..k).
pub fn state_after_rounds(block: &[u8; 128], k: usize) -> [u64; 8] {
    let w: [u64; 16] = core::array::from_fn(|t| u64::from_be_bytes(block[8 * t..8 * t + 8].try_into().unwrap()));
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = IV384;
    for t in 0..k.min(16) {
        let s1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
        let ch = (e & f) ^ (!e & g);
        let t1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[t]).wrapping_add(w[t]);
        let s0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(maj);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    [a, b, c, d, e, f, g, h]
}

/// SHA-384 of 16 already padded single-block messages that agree on message words 0..k, given
/// `s_k = state_after_rounds(block, k)` (the first k rounds are skipped; the result is the
/// plain SHA-384 of each message).
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
pub fn sha384_x16_blocks_from(s_k: &[u64; 8], k: usize, blocks: &[[u8; 128]; 16]) -> [[u8; 48]; 16] {
    use core::arch::x86_64::*;
    unsafe {
        let mut w16 = [[[0u64; 8]; 16]; 2];
        for (li, blk) in blocks.iter().enumerate() {
            let (g, l) = (li / 8, li % 8);
            for t in 0..16 {
                w16[g][t][l] = u64::from_be_bytes(blk[8 * t..8 * t + 8].try_into().unwrap());
            }
        }
        let iv: [__m512i; 8] = core::array::from_fn(|i| _mm512_set1_epi64(IV384[i] as i64));
        let sk: [__m512i; 8] = core::array::from_fn(|i| _mm512_set1_epi64(s_k[i] as i64));
        let mut st = [iv; 2];
        x16::compress2_from(&mut st, [sk; 2], k, &w16);
        let mut words = [[[0u64; 8]; 8]; 2];
        for g in 0..2 {
            for i in 0..8 {
                _mm512_storeu_si512(words[g][i].as_mut_ptr() as *mut _, st[g][i]);
            }
        }
        core::array::from_fn(|li| {
            let (g, l) = (li / 8, li % 8);
            let mut out = [0u8; 48];
            for i in 0..6 {
                out[8 * i..8 * i + 8].copy_from_slice(&words[g][i][l].to_be_bytes());
            }
            out
        })
    }
}

/// SHA-384 of 16 single-block-or-longer messages of equal length (two interleaved 8-lane
/// groups).
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
pub fn sha384_x16(msgs: [&[u8]; 16]) -> [[u8; 48]; 16] {
    use core::arch::x86_64::*;
    let len = msgs[0].len();
    debug_assert!(msgs.iter().all(|m| m.len() == len));
    let nblocks = (len + 17).div_ceil(128);
    unsafe {
        let mut st: [[__m512i; 8]; 2] = [core::array::from_fn(|i| _mm512_set1_epi64(IV384[i] as i64)); 2];
        let mut w16 = [[[0u64; 8]; 16]; 2];
        let mut blk = [0u8; 128];
        for bi in 0..nblocks {
            for (li, m) in msgs.iter().enumerate() {
                let (g, l) = (li / 8, li % 8);
                let off = bi * 128;
                if off + 128 <= len {
                    for t in 0..16 {
                        w16[g][t][l] = u64::from_be_bytes(m[off + 8 * t..off + 8 * t + 8].try_into().unwrap());
                    }
                } else {
                    blk.fill(0);
                    if off < len {
                        blk[..len - off].copy_from_slice(&m[off..]);
                    }
                    if off <= len && len < off + 128 {
                        blk[len - off] = 0x80;
                    }
                    if bi == nblocks - 1 {
                        blk[112..128].copy_from_slice(&((len as u128) * 8).to_be_bytes());
                    }
                    for t in 0..16 {
                        w16[g][t][l] = u64::from_be_bytes(blk[8 * t..8 * t + 8].try_into().unwrap());
                    }
                }
            }
            x16::compress2(&mut st, &w16);
        }
        let mut words = [[[0u64; 8]; 8]; 2];
        for g in 0..2 {
            for i in 0..8 {
                _mm512_storeu_si512(words[g][i].as_mut_ptr() as *mut _, st[g][i]);
            }
        }
        core::array::from_fn(|li| {
            let (g, l) = (li / 8, li % 8);
            let mut out = [0u8; 48];
            for i in 0..6 {
                out[8 * i..8 * i + 8].copy_from_slice(&words[g][i][l].to_be_bytes());
            }
            out
        })
    }
}

/// SHA-384 of 8 messages of equal length.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
pub fn sha384_x8(msgs: [&[u8]; 8]) -> [[u8; 48]; 8] {
    use core::arch::x86_64::*;
    let len = msgs[0].len();
    debug_assert!(msgs.iter().all(|m| m.len() == len));
    let nblocks = (len + 17).div_ceil(128);
    unsafe {
        let mut st: [__m512i; 8] = core::array::from_fn(|i| _mm512_set1_epi64(IV384[i] as i64));
        let mut w16 = [[0u64; 8]; 16];
        let mut blk = [0u8; 128];
        for bi in 0..nblocks {
            for (l, m) in msgs.iter().enumerate() {
                let off = bi * 128;
                if off + 128 <= len {
                    for t in 0..16 {
                        w16[t][l] = u64::from_be_bytes(m[off + 8 * t..off + 8 * t + 8].try_into().unwrap());
                    }
                } else {
                    blk.fill(0);
                    if off < len {
                        blk[..len - off].copy_from_slice(&m[off..]);
                    }
                    if off <= len && len < off + 128 {
                        blk[len - off] = 0x80;
                    }
                    if bi == nblocks - 1 {
                        blk[112..128].copy_from_slice(&((len as u128) * 8).to_be_bytes());
                    }
                    for t in 0..16 {
                        w16[t][l] = u64::from_be_bytes(blk[8 * t..8 * t + 8].try_into().unwrap());
                    }
                }
            }
            x8::compress(&mut st, &w16);
        }
        let mut words = [[0u64; 8]; 8];
        for i in 0..8 {
            _mm512_storeu_si512(words[i].as_mut_ptr() as *mut _, st[i]);
        }
        core::array::from_fn(|l| {
            let mut out = [0u8; 48];
            for i in 0..6 {
                out[8 * i..8 * i + 8].copy_from_slice(&words[i][l].to_be_bytes());
            }
            out
        })
    }
}

/// SHA-384 of every message (any lengths): groups of 8 equal-length messages go through the
/// 8-lane kernel, the rest through `sha2`.
pub fn sha384_many(msgs: &[&[u8]]) -> Vec<[u8; 48]> {
    let mut out = vec![[0u8; 48]; msgs.len()];
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
    if mb_enabled() {
        let mut i = 0;
        while i + 16 <= msgs.len() {
            let len = msgs[i].len();
            if msgs[i..i + 16].iter().all(|m| m.len() == len) {
                let r = sha384_x16(core::array::from_fn(|l| msgs[i + l]));
                out[i..i + 16].copy_from_slice(&r);
                i += 16;
            } else {
                break;
            }
        }
        while i + 8 <= msgs.len() {
            let len = msgs[i].len();
            if msgs[i..i + 8].iter().all(|m| m.len() == len) {
                let r = sha384_x8(core::array::from_fn(|l| msgs[i + l]));
                out[i..i + 8].copy_from_slice(&r);
                i += 8;
            } else {
                out[i] = Sha384::digest(msgs[i]).into();
                i += 1;
            }
        }
        for j in i..msgs.len() {
            out[j] = Sha384::digest(msgs[j]).into();
        }
        return out;
    }
    for (o, m) in out.iter_mut().zip(msgs) {
        *o = Sha384::digest(m).into();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rnd(seed: u64, n: usize) -> Vec<u8> {
        let mut s = seed.wrapping_mul(0x9e3779b97f4a7c15) | 1;
        (0..n)
            .map(|_| {
                s ^= s << 13;
                s ^= s >> 7;
                s ^= s << 17;
                s as u8
            })
            .collect()
    }

    #[test]
    fn mb_sha384_matches_sha2() {
        // all padding edge cases around block boundaries, PoW (105/109 B) and node (104 B) sizes
        for len in (0..300).chain([105, 109, 104, 768, 1000, 4096]) {
            let msgs: Vec<Vec<u8>> = (0..19).map(|i| rnd(len as u64 * 31 + i, len)).collect();
            let refs: Vec<&[u8]> = msgs.iter().map(|m| m.as_slice()).collect();
            let got = sha384_many(&refs);
            for (m, g) in msgs.iter().zip(&got) {
                let want: [u8; 48] = Sha384::digest(m).into();
                assert_eq!(&want, g, "len {len}");
            }
        }
        // mixed lengths
        let msgs: Vec<Vec<u8>> = (0..37).map(|i| rnd(i, (i as usize * 13) % 260)).collect();
        let refs: Vec<&[u8]> = msgs.iter().map(|m| m.as_slice()).collect();
        for (m, g) in msgs.iter().zip(sha384_many(&refs)) {
            assert_eq!(<[u8; 48]>::from(Sha384::digest(m)), g);
        }
        eprintln!("mb available: {MB_AVAILABLE}");
    }

    #[test]
    fn mb_hasher_batches_match() {
        use openvm_stark_backend::hasher::MerkleHasher;
        use p3_field::PrimeCharacteristicRing;
        use crate::sha384::config::{ShaHasher as H, F};
        for fl in [false, true] {
            let h = H { final_layer: fl };
            let leaves: Vec<Vec<Vec<F>>> = (0..21u32)
                .map(|i| (0..8u32).map(|t| (0..13u32).map(|j| F::from_u32(i * 1000 + t * 31 + j)).collect()).collect())
                .collect();
            let want: Vec<_> = leaves.iter().map(|r| h.hash_coset(r)).collect();
            assert_eq!(h.hash_coset_batch(&leaves), want);
            let flat: Vec<F> = leaves.iter().flatten().flatten().copied().collect();
            assert_eq!(h.hash_leaves_flat(&flat, 13, 8), want);
            let ds: Vec<_> = want.iter().chain(want.iter()).copied().collect();
            let want2: Vec<_> = ds.chunks_exact(2).map(|p| h.compress(p[0], p[1])).collect();
            assert_eq!(h.compress_pairs(&ds), want2);
        }
    }

    #[test]
    fn mb_pow_message_and_grind_match() {
        use crate::sha384::config::{grind_mb, pow_message, pow_step};
        for seed in 0..6u64 {
            let st: [u8; 48] = rnd(seed + 100, 48).try_into().unwrap();
            for w in [0u32, 1, 77, 0x7fff_ffff] {
                let m = pow_message(&st, &[w]);
                let (want, _) = pow_step(&st, &[w], 0);
                assert_eq!(<[u8; 48]>::from(Sha384::digest(&m)), want);
                let m2 = pow_message(&st, &[3, w]);
                assert_eq!(<[u8; 48]>::from(Sha384::digest(&m2)), pow_step(&st, &[3, w], 0).0);
            }
            for bits in [8usize, 13, 17] {
                for wide in [false, true] {
                    let got = grind_mb(&st, bits, wide);
                    // reference: the scalar search order (w0 = 0, w ascending)
                    let want = (0u32..).find(|&w| {
                        let wit = if wide { vec![0, w] } else { vec![w] };
                        pow_step(&st, &wit, bits).1
                    }).unwrap();
                    let want = if wide { vec![0, want] } else { vec![want] };
                    assert_eq!(got, want, "seed {seed} bits {bits} wide {wide}");
                }
            }
        }
    }
}
