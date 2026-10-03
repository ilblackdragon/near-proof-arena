//! Frozen shared types for NEAR Proof Arena. See `docs/CONTRACTS.md`.
//!
//! Every hashed object uses RFC 8785-style canonical JSON (`canonical_json`)
//! and contains no floating point values.

pub mod candidate;
pub mod canonical;
pub mod challenge;
pub mod evidence;
pub mod pipeline;
pub mod security;

pub use candidate::CandidateManifest;
pub use canonical::{canonical_json, sha256_digest, Digest};
pub use challenge::{ChallengeDefinition, ChallengeId};
pub use evidence::EvidenceGraph;
pub use pipeline::*;
pub use security::SecurityProfile;

/// Version of the contracts in this crate. Bump on any change to a hashed or
/// wire-visible structure.
pub const SCHEMA_VERSION: &str = "arena-contracts-v1";
