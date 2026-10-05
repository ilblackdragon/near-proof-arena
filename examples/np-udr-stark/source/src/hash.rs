//! The protocol oracle and the wide hash.
//!
//! * `H(m) = SHA-256("NPAI-RO-v1" ‖ m)` (32 bytes) — exactly
//!   `ArenaCore.Interp.deployedRO`.
//! * `WH(tag, m) = H(tag ‖ 0x01 ‖ m) ‖ H(tag ‖ 0x02 ‖ m)` (64 bytes).
//!
//! Single-byte domain tags (first byte of every oracle input):

use sha2::{Digest, Sha256};

pub const RO_TAG: &[u8] = b"NPAI-RO-v1";

pub const TAG_INIT: u8 = 0x00;
pub const TAG_LEAF: u8 = 0x01;
pub const TAG_NODE: u8 = 0x02;
pub const TAG_ABS: u8 = 0x03;
pub const TAG_CHAL: u8 = 0x04;
pub const TAG_QUERY: u8 = 0x05;

pub type Digest32 = [u8; 32];
pub type Digest64 = [u8; 64];

/// `H(parts[0] ‖ parts[1] ‖ …)`.
#[inline]
pub fn h(parts: &[&[u8]]) -> Digest32 {
    let mut s = Sha256::new();
    s.update(RO_TAG);
    for p in parts {
        s.update(p);
    }
    s.finalize().into()
}

/// `WH(tag, parts[0] ‖ parts[1] ‖ …)`.
#[inline]
pub fn wh(tag: u8, parts: &[&[u8]]) -> Digest64 {
    let mut s1 = Sha256::new();
    s1.update(RO_TAG);
    s1.update([tag, 0x01]);
    let mut s2 = Sha256::new();
    s2.update(RO_TAG);
    s2.update([tag, 0x02]);
    for p in parts {
        s1.update(p);
        s2.update(p);
    }
    let mut out = [0u8; 64];
    out[..32].copy_from_slice(&s1.finalize());
    out[32..].copy_from_slice(&s2.finalize());
    out
}

/// Plain SHA-256 (not the oracle), e.g. for the public-tape digest.
pub fn sha256(m: &[u8]) -> Digest32 {
    Sha256::digest(m).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ro_is_prefixed_sha() {
        let mut m = RO_TAG.to_vec();
        m.extend_from_slice(b"abc");
        assert_eq!(h(&[b"abc"]), sha256(&m));
        let w = wh(7, &[b"x", b"y"]);
        assert_eq!(&w[..32], &h(&[&[7, 1], b"xy"]));
        assert_eq!(&w[32..], &h(&[&[7, 2], b"xy"]));
    }
}
