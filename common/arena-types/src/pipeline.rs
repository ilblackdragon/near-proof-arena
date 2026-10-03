use crate::{challenge::Tier, Digest, EvidenceGraph};
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
