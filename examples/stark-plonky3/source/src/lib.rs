//! `stark-plonky3`: a custom Plonky3 STARK for
//! `near/pv86/receipt-transfer-batch/v0` (hand-written AIRs, see `air/`).

pub mod air;
pub mod config;
pub mod consts;
pub mod engine;
pub mod spec;
pub mod trie;
pub mod wire;

pub use sha2::{Digest as _, Sha256};

/// SHA-256 of `b`.
#[inline]
pub fn sha256(b: &[u8]) -> [u8; 32] {
    use sha2::Digest;
    Sha256::digest(b).into()
}
pub mod eval;
pub mod proof;
pub mod trace;
pub mod witness;
