//! Job types: the single source is `server/arena-jobs` (re-exported here).
//! Only worker-internal helpers are defined locally.

pub use arena_jobs::{
    BuildJob, BuildOutputs, ExecJob, ExecutionInfo, FormalCheckJob, JobContext, JobKind, JobResult,
    JobSpec, LeasedJob, ValidateJob,
};
use arena_types::{ChallengeDefinition, Digest};

/// Limits for running entry points, from the challenge's `resource_limits`
/// and `claim_encoding` (+ worker-side caps on pids / scratch).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunLimits {
    pub max_prepare_ms: u64,
    pub max_prove_ms: u64,
    pub max_verify_ms: u64,
    pub max_ram_bytes: u64,
    pub max_proof_bytes: u64,
    pub max_claim_bytes: u64,
    pub max_request_bytes: u64,
    pub max_witness_bytes: u64,
    pub max_public_artifact_bytes: u64,
    pub max_pids: u32,
    pub scratch_mb: u64,
}

impl RunLimits {
    pub fn from_challenge(c: &ChallengeDefinition) -> Self {
        let r = &c.resource_limits;
        let per_run = if c.measurement.per_run_timeout_ms > 0 {
            c.measurement.per_run_timeout_ms
        } else {
            u64::MAX
        };
        RunLimits {
            max_prepare_ms: r.max_prepare_ms,
            max_prove_ms: r.max_prove_ms.min(per_run),
            max_verify_ms: r.max_verify_ms,
            max_ram_bytes: r.max_ram_bytes,
            max_proof_bytes: r.max_proof_bytes,
            max_claim_bytes: c.claim_encoding.max_claim_bytes,
            max_request_bytes: c.claim_encoding.max_request_bytes,
            max_witness_bytes: c.claim_encoding.max_witness_bytes,
            max_public_artifact_bytes: r.max_public_artifact_bytes,
            max_pids: 256,
            scratch_mb: ((r.max_proof_bytes
                + c.claim_encoding.max_claim_bytes
                + r.max_public_artifact_bytes)
                >> 20)
                .max(64)
                + 64,
        }
    }
}

/// An artifact produced by a job. Only `stored` ones are reported as
/// `JobResult.artifacts` (the server requires them to be uploaded).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedArtifact {
    pub name: String,
    pub digest: Digest,
    pub public: bool,
    pub stored: bool,
}
