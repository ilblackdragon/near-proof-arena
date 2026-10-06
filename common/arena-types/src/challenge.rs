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
    /// How benchmark invocations are isolated (v1.4, additive; absent ⇒
    /// `vm_per_invocation`, i.e. bench-spec-v1, and not serialized, so
    /// existing challenge ids are unchanged). See docs/BENCHMARK_SPEC.md §4.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub invocation_mode: Option<InvocationMode>,
    /// The pinned calibration binary and its probe rule (v1.8, additive;
    /// docs/BENCHMARK_SPEC.md §6.1). Absent = no in-session calibration (the
    /// live worker before v1.8).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub calibration: Option<CalibrationSpec>,
}

/// The judge calibration workload (bench-spec-v1.6, §6.1): a fixed,
/// deterministic binary (`runners/calibrate`, `arena-calibrate`), pinned by
/// digest, run in the benchmark sandbox on the benchmark CPUs as probes
/// before the session, at the start of every measured round, and after it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CalibrationSpec {
    /// `arena-calibrate-v1`.
    pub workload: String,
    /// sha256 of the static `arena-calibrate` binary; the worker refuses any other.
    pub binary_digest: Digest,
    /// The checksum the workload must print (a wrong one is INFRA).
    pub expected_checksum: String,
    /// Worker threads per probe (= the benchmark vCPUs).
    pub threads: u32,
    /// Timed runs per probe, after one untimed warm-up run, all in one sandbox
    /// instance; the probe is their median.
    pub steps_per_probe: u32,
    /// Probes before and after the session (each).
    pub edge_probes: u32,
    /// Gate: the 90th-percentile step between consecutive probes (ppm).
    pub max_step_ppm: u64,
    /// Gate: MAD / median over all probes of the session (ppm).
    pub max_noise_ppm: u64,
    /// Host admission median of one probe on this hardware profile; when set,
    /// the session median must be within `max_reference_drift_ppm` of it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reference_median_ns: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_reference_drift_ppm: Option<u64>,
}

/// Sandbox-instance granularity of steady-state benchmark runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum InvocationMode {
    /// bench-spec-v1: every `prove` invocation in its own fresh sandbox
    /// instance (a microVM boot per request is inside nothing timed, but the
    /// guest page cache is cold for every invocation).
    VmPerInvocation,
    /// bench-spec-v1.1: each measured batch runs in ONE fresh sandbox
    /// instance; every request is still a fresh process with a wiped scratch,
    /// only its own inputs and no state carried between requests. One
    /// untimed warm-up invocation on the batch's first request precedes the
    /// timed ones. Cold runs stay one instance per invocation.
    VmPerBatch,
}

impl MeasurementProcedure {
    pub fn invocation_mode(&self) -> InvocationMode {
        self.invocation_mode
            .unwrap_or(InvocationMode::VmPerInvocation)
    }
}

/// Parameters of the judge-built admission statement that are not resource
/// limits of the sandbox (`ArenaCore.ChallengeParams`). Optional so that
/// challenges without a formal statement (demo) keep their ids.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct FormalParams {
    /// NPAI fuel given to the approved interpreter for one `verify` call
    /// (`ChallengeParams.verifyFuel`).
    pub verify_fuel: u64,
    /// Honest proof-size bound used by `VerifierComplete`
    /// (`ChallengeParams.maxProofBytes`); must equal `resource_limits.max_proof_bytes`.
    pub max_proof_bytes: u64,
    /// Fuel cap of an explicit standard-model security reduction
    /// (`ChallengeParams.maxReductionFuel`).
    pub max_reduction_fuel: u64,
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
    /// Formal admission-statement parameters (v1.2, additive; absent ⇒ not
    /// serialized, so existing challenge ids are unchanged).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub formal_params: Option<FormalParams>,
    /// Scoring kind and, for `cost_v1`, the pinned price model and reference
    /// cost components (v1.5, additive; absent ⇒ `speed` and not serialized,
    /// so existing challenge ids are unchanged). docs/BENCHMARK_SPEC.md §14.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub scoring: Option<crate::scoring::ScoringSpec>,
    /// Coverage tiers (v1.7, additive; absent ⇒ not serialized, so existing
    /// challenge ids are unchanged). docs/CONTRACTS.md §11.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub coverage: Option<crate::coverage::CoverageSpec>,
    pub supersedes: Option<ChallengeId>,
    pub created_at: String,
}

impl ChallengeDefinition {
    pub fn digest(&self) -> Result<Digest, canonical::CanonicalError> {
        canonical::sha256_digest(self)
    }
    /// Required obligations that decide the run and stop it on `FAIL`
    /// (fail-fast). On `formal` and `demo` tier: every required obligation.
    /// On `experimental` tier the formal obligations and `ARTIFACT_BINDING`
    /// are **diagnostic** (master spec §8: experimental submissions run tests
    /// and collect timings, but get no rank and no formal acceptance): they
    /// are evaluated and reported, never block the test/benchmark stages and
    /// never enter the decision. Build, conformance, adversarial and resource
    /// obligations stay blocking on every tier.
    pub fn blocking_obligations(&self) -> Vec<crate::ObligationId> {
        self.required_obligations
            .iter()
            .copied()
            .filter(|o| self.tier != Tier::Experimental || !o.is_formal())
            .collect()
    }
    /// Required obligations that are reported but non-blocking (see
    /// [`Self::blocking_obligations`]); empty unless `tier = experimental`.
    pub fn diagnostic_obligations(&self) -> Vec<crate::ObligationId> {
        self.required_obligations
            .iter()
            .copied()
            .filter(|o| self.tier == Tier::Experimental && o.is_formal())
            .collect()
    }
    /// The board(s) this challenge has: `speed` always; `cost_v1` when its
    /// `scoring` section pins a price model.
    pub fn scoring_kind(&self) -> crate::scoring::ScoringKind {
        self.scoring
            .as_ref()
            .map(|s| s.kind)
            .unwrap_or(crate::scoring::ScoringKind::Speed)
    }
    /// Validate the optional `scoring` section against this challenge.
    pub fn check_scoring(&self) -> Result<(), String> {
        match &self.scoring {
            None => Ok(()),
            Some(s) => s.validate(self),
        }
    }
    /// Validate the optional `coverage` section against this challenge.
    pub fn check_coverage(&self) -> Result<(), String> {
        match &self.coverage {
            None => Ok(()),
            Some(c) => c.validate(self),
        }
    }
    /// The coverage tier a manifest declares (CONTRACTS §11): `Ok(None)` on a
    /// challenge without coverage and no declaration; an error when the
    /// declaration is missing, unknown, or given for a challenge without
    /// coverage.
    pub fn declared_tier(
        &self,
        m: &crate::CandidateManifest,
    ) -> Result<Option<&crate::coverage::CoverageTier>, String> {
        match (&self.coverage, &m.entry.declared_tier) {
            (None, None) => Ok(None),
            (None, Some(_)) => {
                Err("entry.declared_tier is only valid on a coverage-tiered challenge".into())
            }
            (Some(_), None) => {
                Err("this challenge is coverage-tiered: entry.declared_tier is required".into())
            }
            (Some(c), Some(t)) => c.tier(t).map(Some).ok_or_else(|| {
                format!("entry.declared_tier {t:?} is not a tier of this challenge")
            }),
        }
    }
    /// `chl_` + first 32 hex chars of the canonical digest.
    pub fn id(&self) -> Result<ChallengeId, canonical::CanonicalError> {
        Ok(format!("chl_{}", &self.digest()?.hex()[..32]))
    }
}

#[cfg(test)]
mod blocking_tests {
    use super::Tier;
    use crate::ObligationId::{self, *};

    fn def(tier: Tier, req: Vec<ObligationId>) -> super::ChallengeDefinition {
        let mut d: super::ChallengeDefinition = serde_json::from_str(include_str!(
            "../../../challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json"
        ))
        .unwrap();
        d.tier = tier;
        d.required_obligations = req;
        d
    }

    #[test]
    fn formal_and_demo_block_on_everything_required() {
        let req = vec![
            PkgWellformed,
            ArtifactBinding,
            AxiomAudit,
            ConformanceDifferential,
        ];
        for t in [Tier::Formal, Tier::Demo] {
            let d = def(t, req.clone());
            assert_eq!(d.blocking_obligations(), req);
            assert!(d.diagnostic_obligations().is_empty());
        }
    }

    #[test]
    fn experimental_formal_gates_are_diagnostic() {
        let d = def(
            Tier::Experimental,
            vec![
                PkgWellformed,
                BuildReproducible,
                ArtifactBinding,
                FormalSemanticSoundness,
                AxiomAudit,
                ConformanceDifferential,
                AdversarialProofs,
                ProverReliability,
                ResourceLimits,
                Benchmark,
            ],
        );
        assert_eq!(
            d.blocking_obligations(),
            vec![
                PkgWellformed,
                BuildReproducible,
                ConformanceDifferential,
                AdversarialProofs,
                ProverReliability,
                ResourceLimits,
                Benchmark
            ]
        );
        assert_eq!(
            d.diagnostic_obligations(),
            vec![ArtifactBinding, FormalSemanticSoundness, AxiomAudit]
        );
    }
}
