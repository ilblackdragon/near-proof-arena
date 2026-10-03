use crate::{canonical, Digest, SecurityProfile};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

pub type ChallengeId = String;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum Tier {
    /// Official ranked board; all formal obligations mandatory.
    Formal,
    /// Tests + diagnostic timings only; never ranked as formal.
    Experimental,
    /// Plumbing demonstration; simulated components allowed, always labelled DEMO.
    Demo,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct NearcorePin {
    pub repo: String,
    pub tag: String,
    pub commit: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum ScopeKind {
    FullChunkTransition,
    Subset,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct Restriction {
    pub id: String,
    pub text: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct FormalSpecRef {
    /// Lean module that defines `NearRelation` for this challenge.
    pub relation_module: String,
    /// Fully qualified Lean name of the relation, e.g. `NearSpec.TransferV1.NearRelation`.
    pub relation_decl: String,
    /// Tree digest of `spec/lean` + `formal-core` sources the challenge was frozen against.
    pub tree_digest: Digest,
    /// Lean toolchain, e.g. `leanprover/lean4:v4.x.y`.
    pub lean_toolchain: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct SemanticScope {
    pub name: String,
    pub kind: ScopeKind,
    /// e.g. `single_action_receipt_transition`, `chunk_transition`.
    pub granularity: String,
    pub restrictions: Vec<Restriction>,
    /// Properties explicitly NOT established by an admitted proof.
    pub excludes: Vec<String>,
    pub formal_spec: FormalSpecRef,
    /// Human-readable spec document digest (`spec/<name>.md`).
    pub spec_doc_digest: Digest,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ClaimEncoding {
    pub format: String,
    pub spec_digest: Digest,
    pub max_request_bytes: u64,
    pub max_witness_bytes: u64,
    pub max_claim_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ToolchainPolicy {
    pub lean_toolchain: String,
    /// Digest of the formal checker image (rootfs) used for clean rechecks.
    pub checker_image: Digest,
    /// Exact logical axioms permitted (fully qualified names).
    pub axiom_allowlist: Vec<String>,
    /// Allowed Lean package imports: name -> pinned git commit.
    pub allowed_packages: Vec<(String, String)>,
    /// Independent kernel recheckers that must all accept, e.g. `lean4checker`, `nanoda`.
    pub recheckers: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct HardwareProfile {
    pub id: String,
    pub cpu_model: String,
    pub vcpus: u32,
    pub ram_bytes: u64,
    pub gpu: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct WorkloadClass {
    pub id: String,
    pub description: String,
    /// Weight in parts-per-million; all weights in a suite sum to 1_000_000.
    pub weight_ppm: u32,
    /// Number of requests per measured batch.
    pub batch_size: u32,
    /// Digest of the generator spec (fresh inputs are sampled after freeze).
    pub generator: Digest,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct WorkloadSuite {
    pub revision: String,
    pub classes: Vec<WorkloadClass>,
    /// Public dev fixtures (tree digest). Held-out and fresh inputs are not listed here.
    pub public_fixtures: Digest,
    /// Commitment to the held-out set (digest of its tree), revealed at season end.
    pub heldout_commitment: Digest,
    /// Baseline candidate submission id and per-class baseline medians (ns).
    pub baseline_submission: Option<String>,
    pub baseline_ns: Vec<(String, u64)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct MeasurementProcedure {
    pub warmup_runs: u32,
    pub measured_runs: u32,
    /// `median` only in v1.
    pub aggregation: String,
    /// Runs farther than this many MADs from the median are flagged (not dropped).
    pub outlier_mad_k: u32,
    pub cold_runs: u32,
    pub concurrency: u32,
    pub per_run_timeout_ms: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ResourceLimits {
    pub max_proof_bytes: u64,
    pub max_verify_ms: u64,
    pub max_prove_ms: u64,
    pub max_ram_bytes: u64,
    pub max_vram_bytes: u64,
    pub max_public_artifact_bytes: u64,
    pub max_prepare_ms: u64,
    pub max_build_ms: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ChallengeDefinition {
    pub schema: String,
    pub name: String,
    pub season: String,
    pub tier: Tier,
    pub nearcore: NearcorePin,
    pub protocol_version: u32,
    pub chain_id: String,
    pub runtime_config_digest: Digest,
    pub semantic_scope: SemanticScope,
    pub claim_encoding: ClaimEncoding,
    pub security_profile: SecurityProfile,
    pub toolchain_policy: ToolchainPolicy,
    pub required_obligations: Vec<crate::ObligationId>,
    /// Gates that may be `NOT_APPLICABLE` under this challenge (e.g. FORMAL_ZK
    /// for validity-only profiles).
    pub not_applicable_gates: Vec<crate::ObligationId>,
    pub hardware_profile: HardwareProfile,
    pub workload_suite: WorkloadSuite,
    pub measurement: MeasurementProcedure,
    pub resource_limits: ResourceLimits,
    pub supersedes: Option<ChallengeId>,
    pub created_at: String,
}

impl ChallengeDefinition {
    pub fn digest(&self) -> Result<Digest, canonical::CanonicalError> {
        canonical::sha256_digest(self)
    }
    /// `chl_` + first 32 hex chars of the canonical digest.
    pub fn id(&self) -> Result<ChallengeId, canonical::CanonicalError> {
        Ok(format!("chl_{}", &self.digest()?.hex()[..32]))
    }
}
