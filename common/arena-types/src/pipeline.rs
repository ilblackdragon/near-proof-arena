use crate::{challenge::Tier, Digest, EvidenceGraph, VerifyRoute};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, JsonSchema,
)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum ObligationId {
    PkgWellformed,
    BuildReproducible,
    ArtifactBinding,
    FormalSemanticSoundness,
    FormalSemanticCompleteness,
    FormalCryptoSoundness,
    FormalImplConnection,
    FormalZk,
    AxiomAudit,
    ConformanceDifferential,
    AdversarialProofs,
    ProverReliability,
    ResourceLimits,
    Benchmark,
}

impl ObligationId {
    /// Formal obligations and `ARTIFACT_BINDING`: the gates the FORMAL_CHECK
    /// stage decides (they all need a certificate about the built artifacts).
    pub fn is_formal(self) -> bool {
        use ObligationId::*;
        matches!(
            self,
            ArtifactBinding
                | FormalSemanticSoundness
                | FormalSemanticCompleteness
                | FormalCryptoSoundness
                | FormalImplConnection
                | FormalZk
                | AxiomAudit
        )
    }
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, JsonSchema,
)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum Stage {
    Received,
    Validated,
    Built,
    FormalChecked,
    ConformanceChecked,
    Benchmarked,
    Decided,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum Decision {
    Admitted,
    Rejected,
    Inconclusive,
    InfraError,
    Cancelled,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum GateStatus {
    Pass,
    Fail,
    Unknown,
    NotApplicable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum ReasonCode {
    ManifestInvalid,
    ArchiveUnsafe,
    ChallengeUnknown,
    ProfileNotAllowed,
    BuildFailed,
    BuildNotReproducible,
    CertificateMissing,
    TheoremTypeMismatch,
    UnapprovedAssumption,
    ForbiddenAxiom,
    SorryFound,
    NativeEvalFound,
    ShadowedDefinition,
    RecheckFailed,
    ArtifactBindingFailed,
    ClaimMismatch,
    CounterexampleFound,
    HostileProofAccepted,
    VerifierNondeterministic,
    ProverFailed,
    ResourceLimit,
    Timeout,
    SandboxViolation,
    SecurityBoundInsufficient,
    ObligationUndischarged,
    DemoOnly,
    InfraError,
    Cancelled,
    /// v1.7 (coverage-tiered challenges): `prove` answered `UNSUPPORTED` on a
    /// positive case of a class its declared tier is complete for.
    CoverageGapInTier,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct EvidenceRef {
    pub label: String,
    pub digest: Digest,
    /// Whether this artifact may be shown publicly (held-out data must not).
    pub public: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct GateResult {
    /// Gate id; equals the obligation id for obligation gates.
    pub gate: ObligationId,
    pub mandatory: bool,
    pub status: GateStatus,
    pub reason_codes: Vec<ReasonCode>,
    /// Bounded, sanitized, plain text (never HTML).
    pub summary: String,
    pub evidence: Vec<EvidenceRef>,
    pub started_at: Option<String>,
    pub finished_at: Option<String>,
    /// Set when the result was reused from a parent via the content-addressed cache.
    pub reused_from: Option<String>,
}

/// Change classification, computed by the judge (never trusted from the agent).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum ChangeClass {
    NoParent,
    ProverOnly,
    VerifierOrProtocol,
}

/// The digests that define the *verified* surface. If all are equal between a
/// child and its parent, formal results may be reused (`ProverOnly`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct VerifiedSurface {
    pub challenge_id: String,
    pub verify_artifact: Digest,
    pub prepare_artifact: Digest,
    pub public_artifacts: Digest,
    pub formal_tree: Digest,
    pub certificate_decl: String,
    pub checker_image: Digest,
    // ---- additive (v1.3, red-team finding RT-01) ----
    // Everything below changes the judge-built admission statement (the
    // `art.impl` of `Judge.Expected`) or which code runs as `verify`, so it
    // must be part of the surface: otherwise a child that swaps only its NPAI
    // bytecode or its native-lean model would hit the parent's formal-cache
    // entry and inherit formal PASSes that were never checked for it.
    /// Effective verify route (`native` when the manifest omits it).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verify_route: Option<VerifyRoute>,
    /// `npai-v1`: SHA-256 digest of the built verifier bytecode image.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verifier_bytecode: Option<Digest>,
    /// `native-lean`: `[formal] verifier_model`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verifier_model: Option<String>,
    /// `native-lean`: `[formal] verifier_model_module`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verifier_model_module: Option<String>,
    // ---- additive (v1.7) ----
    // The declared coverage tier selects the admission statement's params
    // (CONTRACTS §11): a different tier is a different formal surface.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub declared_tier: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct ClassMeasurement {
    pub class_id: String,
    pub weight_ppm: u32,
    pub runs_ns: Vec<u64>,
    pub median_ns: u64,
    pub mad_ns: u64,
    pub cold_ns: Option<u64>,
    pub baseline_ns: u64,
    pub verify_median_ns: u64,
    pub proof_bytes_max: u64,
    pub peak_rss_bytes: u64,
    /// Per measured run (same order as `runs_ns`): Σ verify wall ns of the
    /// batch's proofs (v1.5, additive; empty in older results).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub verify_runs_ns: Vec<u64>,
    /// Per measured run: Σ proof bytes of the batch (v1.5, additive).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub proof_bytes_runs: Vec<u64>,
    /// v1.7 (coverage-tiered challenges only): `prove` answered `UNSUPPORTED`
    /// in this class, so it carries no timing (all time fields 0) and is
    /// excluded from the score with the weights renormalized (BENCHMARK_SPEC §17).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub abstained: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct BenchmarkResult {
    pub hardware_profile: String,
    pub suite_revision: String,
    pub classes: Vec<ClassMeasurement>,
    /// Score * 1000 as integer (e.g. 100000 == 100.000).
    pub score_milli: Option<u64>,
    /// Half-width of a bootstrap 95% interval, milli units.
    pub score_ci_milli: Option<u64>,
    pub prepare_ns: u64,
    pub public_artifact_bytes: u64,
    pub measured_by: String,
    /// Cost-board result for `scoring.kind = cost_v1` challenges (v1.5,
    /// additive). Never compared with `score_milli` (a speed score).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cost: Option<crate::scoring::CostResult>,
}

/// Public view of a submission (API `GET /v1/submissions/{id}`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct SubmissionView {
    pub id: String,
    pub challenge_id: String,
    pub agent: String,
    pub candidate_name: String,
    pub backend_family: String,
    pub parent: Option<String>,
    pub tier: Tier,
    pub package_digest: Digest,
    pub stage: Stage,
    pub decision: Option<Decision>,
    /// `null` while pending; `true` only if every mandatory gate passed.
    pub accepted: Option<bool>,
    pub score_milli: Option<u64>,
    pub change_class: Option<ChangeClass>,
    pub gates: Vec<GateResult>,
    pub reason_codes: Vec<ReasonCode>,
    pub benchmark: Option<BenchmarkResult>,
    pub evidence_graph: Option<EvidenceGraph>,
    pub revoked: Option<Revocation>,
    pub created_at: String,
    pub updated_at: String,
    // ---- additive, optional (v1.1; see docs/CHANGELOG-contracts.md) ----
    /// Public artifacts produced by the judge for this run.
    #[serde(default)]
    pub artifacts: Vec<ArtifactRef>,
    /// Verified-surface digests (set once the judge build completed).
    #[serde(default)]
    pub verified_surface: Option<VerifiedSurface>,
    #[serde(default)]
    pub build: Option<BuildInfo>,
    /// Assumptions the admission may rely on (the challenge's security profile).
    #[serde(default)]
    pub assumptions: Vec<AssumptionRef>,
    /// Trusted computing base entries the result depends on.
    #[serde(default)]
    pub trusted_base: Vec<TrustedBaseEntry>,
    /// Bounded, sanitized plain-text log excerpts (never HTML).
    #[serde(default)]
    pub logs: Vec<LogExcerpt>,
    #[serde(default)]
    pub revocation_history: Vec<RevocationEvent>,
    // ---- additive, optional (v1.7) ----
    /// Coverage-tiered challenges: the declared tier and proven coverage
    /// (CONTRACTS §11).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub coverage: Option<crate::coverage::CoverageReport>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct ArtifactRef {
    pub label: String,
    pub digest: Digest,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct BuildInfo {
    /// Build sandbox image/rootfs digest or id, if reported.
    pub toolchain_image: Option<String>,
    /// `BUILD_REPRODUCIBLE` passed (two judge builds bit-identical).
    pub reproducible: bool,
    pub build_ns: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct AssumptionRef {
    pub id: String,
    pub lean_decl: Option<String>,
    pub description: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct TrustedBaseEntry {
    pub id: String,
    pub label: String,
    pub digest: Option<Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct LogExcerpt {
    /// Log name, e.g. `BUILD` or `BUILD/error`.
    pub name: String,
    /// Pipeline stage / job kind the log belongs to.
    pub stage: String,
    pub text: String,
    pub truncated: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct RevocationEvent {
    /// `revoked` (v1 has no un-revoke).
    pub action: String,
    pub reason: String,
    pub at: String,
    pub by: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct Revocation {
    pub reason: String,
    pub revoked_at: String,
    pub revoked_by: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct LeaderboardEntry {
    pub rank: Option<u32>,
    pub submission_id: String,
    pub agent: String,
    pub candidate_name: String,
    pub backend_family: String,
    pub tier: Tier,
    pub decision: Option<Decision>,
    pub accepted: Option<bool>,
    pub score_milli: Option<u64>,
    pub prove_median_ns: Option<u64>,
    pub verify_median_ns: Option<u64>,
    pub proof_bytes: Option<u64>,
    pub peak_rss_bytes: Option<u64>,
    pub hardware_profile: String,
    pub scope: String,
    pub security_profile: String,
    pub submitted_at: String,
    pub revoked: bool,
    /// Half-width of the score's 95% interval, milli units (additive, v1.1).
    #[serde(default)]
    pub score_ci_milli: Option<u64>,
    /// The challenge this result was measured under (additive, v1.4). A
    /// result is never re-labelled or moved to another challenge's board.
    #[serde(default)]
    pub challenge_id: String,
    /// That challenge's NEAR protocol version (additive, v1.4).
    #[serde(default)]
    pub protocol_version: u32,
    /// Set when the challenge has been superseded: the board is historical
    /// (frozen, closed for new submissions) and scores are not comparable
    /// with the successor's (additive, v1.4).
    #[serde(default)]
    pub superseded_by: Option<String>,
    /// Which board `rank` belongs to: `speed` (default) or `cost_v1`
    /// (additive, v1.5).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub board: Option<crate::scoring::ScoringKind>,
    /// Cost-board score and its CI (cost_v1 challenges only; v1.5).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cost_score_milli: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cost_score_ci_milli: Option<u64>,
    /// Per-class cost components, so the board shows why (v1.5).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cost: Option<crate::scoring::CostResult>,
    // ---- additive (v1.7, coverage-tiered challenges only) ----
    /// Declared coverage tier; the board orders by its rank first.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub declared_tier: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tier_rank: Option<u32>,
    /// `coverage.conformance.share_ppm` of the ranked run.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub coverage_share_ppm: Option<u32>,
}

/// Pure decision function shared by server and tests.
/// `gates` must contain every mandatory gate that was scheduled.
pub fn decide(
    gates: &[GateResult],
    required: &[ObligationId],
    not_applicable_allowed: &[ObligationId],
) -> (Decision, bool) {
    let mut unknown = false;
    for req in required {
        match gates.iter().find(|g| g.gate == *req) {
            None => unknown = true,
            Some(g) => match g.status {
                GateStatus::Pass => {}
                GateStatus::Fail => return (Decision::Rejected, false),
                GateStatus::Unknown => unknown = true,
                GateStatus::NotApplicable => {
                    if !not_applicable_allowed.contains(req) {
                        return (Decision::Rejected, false);
                    }
                }
            },
        }
    }
    for g in gates.iter().filter(|g| g.mandatory) {
        if g.status == GateStatus::Fail {
            return (Decision::Rejected, false);
        }
        if g.status == GateStatus::Unknown {
            unknown = true;
        }
    }
    if unknown {
        (Decision::Inconclusive, false)
    } else {
        (Decision::Admitted, true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn g(gate: ObligationId, status: GateStatus) -> GateResult {
        GateResult {
            gate,
            mandatory: true,
            status,
            reason_codes: vec![],
            summary: String::new(),
            evidence: vec![],
            started_at: None,
            finished_at: None,
            reused_from: None,
        }
    }
    use ObligationId::*;
    #[test]
    fn missing_mandatory_is_not_pass() {
        let (d, a) = decide(
            &[g(PkgWellformed, GateStatus::Pass)],
            &[PkgWellformed, AxiomAudit],
            &[],
        );
        assert_eq!((d, a), (Decision::Inconclusive, false));
    }
    #[test]
    fn na_only_if_allowed() {
        let gates = [g(FormalZk, GateStatus::NotApplicable)];
        assert_eq!(decide(&gates, &[FormalZk], &[]).0, Decision::Rejected);
        assert_eq!(
            decide(&gates, &[FormalZk], &[FormalZk]).0,
            Decision::Admitted
        );
    }
    #[test]
    fn fail_dominates_unknown() {
        let gates = [
            g(AxiomAudit, GateStatus::Unknown),
            g(Benchmark, GateStatus::Fail),
        ];
        assert_eq!(
            decide(&gates, &[AxiomAudit, Benchmark], &[]).0,
            Decision::Rejected
        );
    }
}
