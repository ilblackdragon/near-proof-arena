//! Native reference for the SHA-512 compression (FIPS 180-4), checked against
//! `sha2::compress512`.  Identical to v2.1's (the NV crate copy uses `compress2_trace`).
use crate::s384::air::K;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Comp {
    pub h: [u64; 8],
    pub block: [u64; 16],
}

pub const SHA384_IV: [u64; 8] = [
    0xcbbb9d5dc1059ed8,
    0x629a292a367cd507,
    0x9159015a3070dd17,
    0x152fecd8f70e5939,
    0x67332667ffc00b31,
    0x8eb44a8768581511,
    0xdb0c2e0d64f98fa7,
    0x47b5481dbefa4fa4,
];
pub const SHA512_IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

/// Reference: sha2 crate compression.
pub fn sha2_compress(c: &Comp) -> [u64; 8] {
    let mut st = c.h;
    let bytes: Vec<u8> = c.block.iter().flat_map(|w| w.to_be_bytes()).collect();
    let blk = sha2::digest::generic_array::GenericArray::clone_from_slice(&bytes);
    sha2::compress512(&mut st, &[blk]);
    st
}

/// Message padding (FIPS 180-4 §5.1.2) into 1024-bit blocks.
pub fn pad_message(msg: &[u8]) -> Vec<[u64; 16]> {
    let mut m = msg.to_vec();
    m.push(0x80);
    while m.len() % 128 != 112 {
        m.push(0);
    }
    m.extend_from_slice(&(0u64).to_be_bytes());
    m.extend_from_slice(&((msg.len() as u64) * 8).to_be_bytes());
    m.chunks(128)
        .map(|ch| std::array::from_fn(|i| u64::from_be_bytes(ch[8 * i..8 * i + 8].try_into().unwrap())))
        .collect()
}

pub fn bsig0(x: u64) -> u64 {
    x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39)
}
pub fn bsig1(x: u64) -> u64 {
    x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41)
}
pub fn ssig0(x: u64) -> u64 {
    x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7)
}
pub fn ssig1(x: u64) -> u64 {
    x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6)
}
pub fn chf(e: u64, f: u64, g: u64) -> u64 {
    (e & f) ^ (!e & g)
}
pub fn majf(a: u64, b: u64, c: u64) -> u64 {
    (a & b) ^ (a & c) ^ (b & c)
}

/// Words of one compression: a[-4..80), e[-4..80) (index +4), W[0..80), output.
pub struct Words {
    pub a: [u64; 84],
    pub e: [u64; 84],
    pub w: [u64; 80],
    pub out: [u64; 8],
}
pub fn round_words(c: &Comp) -> Words {
    let mut w = [0u64; 80];
    w[..16].copy_from_slice(&c.block);
    for t in 16..80 {
        w[t] = ssig1(w[t - 2]).wrapping_add(w[t - 7]).wrapping_add(ssig0(w[t - 15])).wrapping_add(w[t - 16]);
    }
    let mut a = [0u64; 84];
    let mut e = [0u64; 84];
    for k in 0..4 {
        a[3 - k] = c.h[k]; // a[-1] = H0 ... a[-4] = H3
        e[3 - k] = c.h[4 + k];
    }
    for t in 0..80 {
        let i = t + 4;
        let t1 = e[i - 4]
            .wrapping_add(bsig1(e[i - 1]))
            .wrapping_add(chf(e[i - 1], e[i - 2], e[i - 3]))
            .wrapping_add(K[t])
            .wrapping_add(w[t]);
        let t2 = bsig0(a[i - 1]).wrapping_add(majf(a[i - 1], a[i - 2], a[i - 3]));
        a[i] = t1.wrapping_add(t2);
        e[i] = a[i - 4].wrapping_add(t1);
    }
    let mut out = [0u64; 8];
    for k in 0..4 {
        out[k] = c.h[k].wrapping_add(a[83 - k]);
        out[4 + k] = c.h[4 + k].wrapping_add(e[83 - k]);
    }
    Words { a, e, w, out }
}

/// Deterministic xorshift for test inputs (no extra dependency).
pub struct Rng(pub u64);
impl Rng {
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    pub fn comp(&mut self) -> Comp {
        Comp { h: std::array::from_fn(|_| self.next()), block: std::array::from_fn(|_| self.next()) }
    }
}
