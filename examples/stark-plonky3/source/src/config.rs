//! The STARK configuration: field, extension, hash, PCS and FRI parameters.
//!
//! Every cryptographic object in the proof is built from SHA-256 only, so the
//! Fiat–Shamir / Merkle assumptions are the challenge profile's approved
//! `sha256_cr` / `sha256_rom`:
//!
//! * leaves: `SerializingHasher<Sha256>` (full SHA-256 of the canonical u32
//!   serialisation of the row's field elements);
//! * Merkle nodes: `CompressionFunctionFromHasher<Sha256, 2, 32>` = full
//!   SHA-256 (with padding) of `left ‖ right`;
//! * transcript: `SerializingChallenger32<KoalaBear, HashChallenger<u8, Sha256, 32>>`.
//!
//! Field: KoalaBear (p = 2^31 − 2^24 + 1); challenges in the degree-8 binomial
//! extension (248 bits). FRI: rate 1/8, binary folding, `NUM_QUERIES` queries,
//! grinding as below. See `security.rs` for the bound computation.

use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_koala_bear::KoalaBear;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_sha256::Sha256;
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher};
use p3_uni_stark::StarkConfig;

pub type Val = KoalaBear;
pub const EXT_DEGREE: usize = 8;
pub type Challenge = BinomialExtensionField<Val, EXT_DEGREE>;
pub type ByteHash = Sha256;
pub type FieldHash = SerializingHasher<ByteHash>;
pub type MyCompress = CompressionFunctionFromHasher<ByteHash, 2, 32>;
pub type ValMmcs = MerkleTreeMmcs<Val, u8, FieldHash, MyCompress, 2, 32>;
pub type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
pub type Dft = Radix2DitParallel<Val>;
pub type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;
pub type MyPcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
pub type MyConfig = StarkConfig<MyPcs, Challenge, Challenger>;

/// FRI / PCS parameters (fixed; part of the verifier's identity).
pub const LOG_BLOWUP: usize = 3;
pub const NUM_QUERIES: usize = 104;
pub const QUERY_POW_BITS: usize = 20;
pub const COMMIT_POW_BITS: usize = 0;
pub const BATCH_POW_BITS: usize = 0;
pub const MAX_LOG_ARITY: usize = 1;
pub const LOG_FINAL_POLY_LEN: usize = 0;
/// Merkle cap height (number of cap levels sent instead of a single root).
pub const CAP_HEIGHT: usize = 0;

/// Transcript domain separator: binds the protocol identity into the
/// Fiat–Shamir transcript before anything else is observed.
pub const TRANSCRIPT_DOMAIN: &[u8] = b"near-arena/stark-plonky3/v1";

pub fn fri_params(mmcs: ChallengeMmcs) -> FriParameters<ChallengeMmcs> {
    FriParameters {
        log_blowup: LOG_BLOWUP,
        log_final_poly_len: LOG_FINAL_POLY_LEN,
        max_log_arity: MAX_LOG_ARITY,
        num_queries: NUM_QUERIES,
        batch_proof_of_work_bits: BATCH_POW_BITS,
        commit_proof_of_work_bits: COMMIT_POW_BITS,
        query_proof_of_work_bits: QUERY_POW_BITS,
        mmcs,
    }
}

pub fn make_config() -> MyConfig {
    let byte_hash = ByteHash {};
    let field_hash = FieldHash::new(byte_hash);
    let compress = MyCompress::new(byte_hash);
    let val_mmcs = ValMmcs::new(field_hash, compress, CAP_HEIGHT);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let pcs = MyPcs::new(dft, val_mmcs, fri_params(challenge_mmcs));
    let challenger = Challenger::from_hasher(TRANSCRIPT_DOMAIN.to_vec(), byte_hash);
    MyConfig::new(pcs, challenger)
}
