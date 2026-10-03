use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum Privacy {
    ValidityOnly,
    ZeroKnowledge,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum AdversaryClass {
    /// Classical PPT adversary. Nothing in this profile implies post-quantum security.
    Classical,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum SecurityModel {
    Standard,
    RandomOracle,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum SetupModel {
    None,
    Transparent,
    ApprovedCeremony,
}

/// Governed security profile (`security/profiles/<id>.json`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct SecurityProfile {
    pub id: String,
    pub privacy: Privacy,
    pub adversary: AdversaryClass,
    pub target_bits: u32,
    pub model: SecurityModel,
    pub setup_model: SetupModel,
    /// Ids into `security/assumptions/*.json`; each pins an exact Lean declaration.
    pub allowed_assumptions: Vec<String>,
    pub max_prover_queries_log2: u32,
    pub max_hash_queries_log2: u32,
    pub max_aggregation_depth: u32,
    pub deployment_proofs_log2: u32,
}

/// Governed cryptographic assumption, pinned to an exact Lean declaration in
/// `formal-core` (`security/assumptions/<id>.json`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct Assumption {
    pub id: String,
    pub description: String,
    /// Fully qualified Lean name of the hypothesis *definition* (a `Prop`-valued
    /// def in formal-core), e.g. `Arena.Assumptions.Sha256CollisionResistant`.
    pub lean_decl: String,
    /// Digest of the Lean declaration's exported type+value (filled by the
    /// governance tooling; checked by the formal checker).
    pub lean_decl_digest: Option<crate::Digest>,
    pub references: Vec<String>,
}
