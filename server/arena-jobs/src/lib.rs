//! Job payload and result types exchanged between the arena control plane and
//! workers over the narrow worker HTTP API (`/internal/v1/...`).
//!
//! Workers never get database credentials or the report signing key. Every
//! piece of information a worker needs to run a stage is contained in the
//! [`JobSpec`] it leases; everything it produced is returned in a
//! [`JobResult`]. Large artifacts move through the content-addressed artifact
//! endpoints (`GET`/`PUT /internal/v1/artifacts/{digest}`).
//!
//! The control plane treats worker results as *judge* output (workers are part
//! of the judge's trusted base), but it still re-validates their shape: a
//! worker may only report the gates its job kind owns ([`JobKind::owned_gates`]),
//! `mandatory` is recomputed from the challenge, `reused_from` is ignored, all
//! strings are sanitized, and the effective tier is capped by both the
//! worker's registered capability and the result's own `tier_cap`.

#[cfg(feature = "client")]
pub mod client;
pub mod sanitize;

use arena_types::{
    challenge::Tier, BenchmarkResult, CandidateManifest, ChallengeDefinition, Digest,
    EvidenceGraph, EvidenceRef, GateResult, ObligationId, Stage, VerifiedSurface,
};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::str::FromStr;

/// Version tag of the job protocol. Workers should refuse specs they do not understand.
pub const JOB_PROTOCOL_VERSION: &str = "arena-jobs-v1";

/// Kind of a pipeline stage job.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize, JsonSchema,
)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum JobKind {
    Validate,
    Build,
    FormalCheck,
    Conformance,
    Adversarial,
    Benchmark,
}

impl JobKind {
    pub const ALL: [JobKind; 6] = [
        JobKind::Validate,
        JobKind::Build,
        JobKind::FormalCheck,
        JobKind::Conformance,
        JobKind::Adversarial,
        JobKind::Benchmark,
    ];

    /// The gates a job of this kind is allowed (and expected) to report.
    pub fn owned_gates(self) -> &'static [ObligationId] {
        use ObligationId::*;
        match self {
            JobKind::Validate => &[PkgWellformed],
            JobKind::Build => &[BuildReproducible],
            JobKind::FormalCheck => &[
                ArtifactBinding,
                FormalSemanticSoundness,
                FormalSemanticCompleteness,
                FormalCryptoSoundness,
                FormalImplConnection,
                FormalZk,
                AxiomAudit,
            ],
            JobKind::Conformance => &[ConformanceDifferential, ProverReliability, ResourceLimits],
            JobKind::Adversarial => &[AdversarialProofs],
            JobKind::Benchmark => &[Benchmark],
        }
    }

    /// The job kind that owns `gate`.
    pub fn owner_of(gate: ObligationId) -> JobKind {
        Self::ALL
            .into_iter()
            .find(|k| k.owned_gates().contains(&gate))
            .expect("every obligation has an owning job kind")
    }

    /// Pipeline stage reached when all jobs of this stage completed.
    pub fn stage_after(self) -> Stage {
        match self {
            JobKind::Validate => Stage::Validated,
            JobKind::Build => Stage::Built,
            JobKind::FormalCheck => Stage::FormalChecked,
            JobKind::Conformance | JobKind::Adversarial => Stage::ConformanceChecked,
            JobKind::Benchmark => Stage::Benchmarked,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            JobKind::Validate => "VALIDATE",
            JobKind::Build => "BUILD",
            JobKind::FormalCheck => "FORMAL_CHECK",
            JobKind::Conformance => "CONFORMANCE",
            JobKind::Adversarial => "ADVERSARIAL",
            JobKind::Benchmark => "BENCHMARK",
        }
    }
}

impl fmt::Display for JobKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for JobKind {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, String> {
        Self::ALL
            .into_iter()
            .find(|k| k.as_str() == s)
            .ok_or_else(|| format!("unknown job kind {s:?}"))
    }
}

/// Context common to every job of a run.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct JobContext {
    pub submission_id: String,
    pub run_id: String,
    pub challenge_id: String,
    pub challenge_digest: Digest,
    /// Tier of the challenge. A worker whose sandbox cannot satisfy this tier
    /// must refuse the job (the control plane never leases it to one).
    pub tier: Tier,
    /// Digest of the uploaded candidate package archive (fetch via the artifact API).
    pub package_digest: Digest,
}

/// Outputs of the judge-run build (and judge-run `prepare`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct BuildOutputs {
    pub prepare: Digest,
    pub prove: Digest,
    pub verify: Digest,
    /// Tree digest of the complete built bundle (all build outputs).
    pub bundle: Digest,
    /// Tree digest of `public_dir` produced by the judge-run `prepare`, frozen by digest.
    pub public_artifacts: Digest,
    /// Tree digest of the candidate's `formal/` Lean project.
    pub formal_tree: Digest,
    /// Lean constant named by the manifest's `[formal].certificate` (empty if none).
    pub certificate_decl: String,
    /// Build sandbox image/rootfs digest or id (informational).
    #[serde(default)]
    pub toolchain_image: Option<String>,
    /// Judge-measured wall time of one build, ns (informational).
    #[serde(default)]
    pub build_ns: Option<u64>,
    /// `verify_route = "npai-v1"`: digest of the built `entry.verifier_bytecode`
    /// file. Required for that route (the server refuses to derive a verified
    /// surface without it).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verifier_bytecode: Option<Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct ValidateJob {
    pub ctx: JobContext,
    pub challenge: ChallengeDefinition,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct BuildJob {
    pub ctx: JobContext,
    pub challenge: ChallengeDefinition,
    pub manifest: CandidateManifest,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct FormalCheckJob {
    pub ctx: JobContext,
    pub challenge: ChallengeDefinition,
    pub manifest: CandidateManifest,
    pub build: BuildOutputs,
    pub verified_surface: VerifiedSurface,
}

/// Payload shared by the post-build execution stages.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct ExecJob {
    pub ctx: JobContext,
    pub challenge: ChallengeDefinition,
    pub manifest: CandidateManifest,
    pub build: BuildOutputs,
}

pub type ConformanceJob = ExecJob;
pub type AdversarialJob = ExecJob;
pub type BenchmarkJob = ExecJob;

/// A leased job specification, tagged by kind.
// Wire type, built once per lease; boxing the large variant buys nothing.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "kind", content = "job", rename_all = "SCREAMING_SNAKE_CASE")]
pub enum JobSpec {
    Validate(ValidateJob),
    Build(BuildJob),
    FormalCheck(FormalCheckJob),
    Conformance(ConformanceJob),
    Adversarial(AdversarialJob),
    Benchmark(BenchmarkJob),
}

impl JobSpec {
    pub fn kind(&self) -> JobKind {
        match self {
            JobSpec::Validate(_) => JobKind::Validate,
            JobSpec::Build(_) => JobKind::Build,
            JobSpec::FormalCheck(_) => JobKind::FormalCheck,
            JobSpec::Conformance(_) => JobKind::Conformance,
            JobSpec::Adversarial(_) => JobKind::Adversarial,
            JobSpec::Benchmark(_) => JobKind::Benchmark,
        }
    }
    pub fn ctx(&self) -> &JobContext {
        match self {
            JobSpec::Validate(j) => &j.ctx,
            JobSpec::Build(j) => &j.ctx,
            JobSpec::FormalCheck(j) => &j.ctx,
            JobSpec::Conformance(j) | JobSpec::Adversarial(j) | JobSpec::Benchmark(j) => &j.ctx,
        }
    }
    pub fn challenge(&self) -> &ChallengeDefinition {
        match self {
            JobSpec::Validate(j) => &j.challenge,
            JobSpec::Build(j) => &j.challenge,
            JobSpec::FormalCheck(j) => &j.challenge,
            JobSpec::Conformance(j) | JobSpec::Adversarial(j) | JobSpec::Benchmark(j) => {
                &j.challenge
            }
        }
    }
}

/// How (and with what isolation) a result was produced. Results produced by
/// the `bwrap-dev` sandbox or by any simulated component must carry
/// `tier_cap = demo`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct ExecutionInfo {
    /// e.g. `firecracker`, `bwrap-dev`.
    pub sandbox_backend: String,
    pub tier_cap: Tier,
    pub worker_version: String,
}

/// Everything a worker reports for one job.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct JobResult {
    /// Gate results for gates owned by this job kind.
    pub gates: Vec<GateResult>,
    /// Artifacts produced (logs, transcripts, exports...), already uploaded via the artifact API.
    pub artifacts: Vec<EvidenceRef>,
    /// Required for `BENCHMARK` jobs that measured something.
    pub benchmark: Option<BenchmarkResult>,
    pub evidence_graph: Option<EvidenceGraph>,
    /// Required for a passing `VALIDATE` job: the parsed, validated manifest.
    pub manifest: Option<CandidateManifest>,
    /// Required for a passing `BUILD` job.
    pub build: Option<BuildOutputs>,
    pub execution: ExecutionInfo,
    /// Short plain-text log excerpt shown publicly (sanitized, bounded to 16 KiB
    /// by the server). Must not contain held-out data.
    #[serde(default)]
    pub log_excerpt: Option<String>,
}

// ---------------------------------------------------------------------------
// Worker HTTP API wire types
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct LeaseRequest {
    /// Job kinds this worker can run (empty = any).
    #[serde(default)]
    pub kinds: Vec<JobKind>,
    /// Requested lease duration (server clamps to its configured bounds).
    #[serde(default)]
    pub lease_seconds: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct LeasedJob {
    pub job_id: String,
    /// Fencing token: must be presented on heartbeat/complete/fail. A new
    /// lease (e.g. after expiry) invalidates older lease ids.
    pub lease_id: String,
    pub submission_id: String,
    pub run_id: String,
    pub kind: JobKind,
    /// 1-based attempt number of this lease.
    pub attempt: u32,
    pub max_attempts: u32,
    pub lease_until: String,
    pub protocol: String,
    pub spec: JobSpec,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct HeartbeatRequest {
    pub lease_id: String,
    #[serde(default)]
    pub extend_seconds: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct HeartbeatResponse {
    pub lease_until: String,
    /// The run was cancelled: stop work and do not call `/complete`.
    pub cancelled: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct CompleteRequest {
    pub lease_id: String,
    pub result: JobResult,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct FailRequest {
    pub lease_id: String,
    /// Infrastructure error description (sanitized and bounded by the server).
    pub error: String,
    /// `true` for transient errors (retried up to `max_attempts`).
    pub retryable: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct AckResponse {
    pub ok: bool,
    pub message: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct ArtifactPutResponse {
    pub digest: Digest,
    pub size_bytes: u64,
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn every_obligation_owned_exactly_once() {
        use ObligationId::*;
        let all = [
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
        ];
        for g in all {
            let owners: Vec<_> = JobKind::ALL
                .into_iter()
                .filter(|k| k.owned_gates().contains(&g))
                .collect();
            assert_eq!(owners.len(), 1, "{g:?}");
        }
    }
    #[test]
    fn kind_roundtrip() {
        for k in JobKind::ALL {
            assert_eq!(k.as_str().parse::<JobKind>().unwrap(), k);
            let j = serde_json::to_string(&k).unwrap();
            assert_eq!(j, format!("\"{}\"", k.as_str()));
        }
    }
}
