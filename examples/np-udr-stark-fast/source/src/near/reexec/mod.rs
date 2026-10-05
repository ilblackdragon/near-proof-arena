//! NEAR re-execution, copied from `examples/reexec-witness/source/src`
//! (`wire.rs`, `spec.rs`, `trie.rs`, `engine.rs`; proof encoding dropped).
//! Used for decoding `request.bin` / `witness.bin` / `claim.bin` and for the
//! claim (`engine::derive_claim`, = `NearSpec.Codec.deriveClaim`).
pub mod engine;
pub mod spec;
pub mod trie;
pub mod wire;

/// SHA-256 of `b`.
#[inline]
pub fn sha256(b: &[u8]) -> [u8; 32] {
    use sha2::Digest;
    sha2::Sha256::digest(b).into()
}
