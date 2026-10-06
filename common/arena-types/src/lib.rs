//! Frozen shared types for NEAR Proof Arena. See `docs/CONTRACTS.md`.
//!
//! Every hashed object uses RFC 8785-style canonical JSON (`canonical_json`)
//! and contains no floating point values.

pub mod candidate;
pub mod canonical;
pub mod challenge;
pub mod coverage;
pub mod evidence;
pub mod pipeline;
pub mod scoring;
pub mod security;
pub mod tree;
pub mod trusted_tree;

pub use candidate::{CandidateManifest, VerifyRoute};
pub use canonical::{canonical_json, sha256_digest, Digest};
pub use challenge::{ChallengeDefinition, ChallengeId, FormalParams};
pub use coverage::{ClassCoverage, CoverageReport, CoverageSection, CoverageSpec, CoverageTier};
pub use evidence::EvidenceGraph;
pub use pipeline::*;
pub use scoring::{CostClass, CostResult, PriceModel, ScoringKind, ScoringSpec, VerifyStatistic};
pub use security::SecurityProfile;
pub use tree::{tree_digest, tree_digest_entries, tree_entries, TreeEntry};

/// Version of the contracts in this crate. Bump on any change to a hashed or
/// wire-visible structure.
pub const SCHEMA_VERSION: &str = "arena-contracts-v1";
