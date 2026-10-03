//! Job payloads executed by the worker (CONTRACTS §4, §6, §9).
//!
//! These are plain structs owned by the runners-core lane so the worker can
//! be built and tested before the server lane's `server/arena-jobs` crate
//! lands; the integrator reconciles the two (a `From` impl or a re-export
//! either way). Everything here is JSON on the wire; no floats anywhere.
//!
//! Every input is referenced **by digest** and fetched from the artifact
//! store; the worker verifies each fetched blob against its digest.

use arena_types::challenge::MeasurementProcedure;
use arena_types::{BenchmarkResult, CandidateManifest, Digest, GateResult};
use serde::{Deserialize, Serialize};

/// A leased job (CONTRACTS §9 `Job { id, submission_id, kind, attempt,
/// lease_until, spec }`; `kind` is the tag of `spec`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Job {
    pub id: String,
    pub submission_id: String,
    pub attempt: u32,
    /// RFC 3339.
    pub lease_until: String,
    pub spec: JobSpec,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum JobSpec {
    Validate(ValidateJob),
    Build(BuildJob),
    Conformance(ConformanceJob),
    Adversarial(AdversarialJob),
    Benchmark(BenchmarkJob),
}

impl JobSpec {
    pub fn kind(&self) -> JobKind {
        match self {
            JobSpec::Validate(_) => JobKind::Validate,
            JobSpec::Build(_) => JobKind::Build,
            JobSpec::Conformance(_) => JobKind::Conformance,
            JobSpec::Adversarial(_) => JobKind::Adversarial,
            JobSpec::Benchmark(_) => JobKind::Benchmark,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum JobKind {
    Validate,
    Build,
    Conformance,
    Adversarial,
    Benchmark,
}

impl JobKind {
    pub const ALL: [JobKind; 5] = [
        JobKind::Validate,
        JobKind::Build,
        JobKind::Conformance,
        JobKind::Adversarial,
        JobKind::Benchmark,
    ];
    pub fn as_str(self) -> &'static str {
        match self {
            JobKind::Validate => "validate",
            JobKind::Build => "build",
            JobKind::Conformance => "conformance",
            JobKind::Adversarial => "adversarial",
            JobKind::Benchmark => "benchmark",
        }
    }
    pub fn parse(s: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|k| k.as_str() == s)
    }
}

/// One oracle case, provided by the spec-oracle lane as content-addressed
/// files. `public = false` cases are held out: their ids and bytes never
/// appear in summaries or public evidence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OracleCase {
    pub id: String,
    pub request: Digest,
    pub witness: Digest,
    pub expected_claim: Digest,
    pub public: bool,
}

/// Entry points (relative to the bundle root), copied from the validated
/// manifest by the control plane.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EntryPoints {
    pub prepare: String,
    pub prove: String,
    pub verify: String,
}

/// Limits for running entry points (from `ChallengeDefinition`
/// `resource_limits` + `claim_encoding`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
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
    pub fn from_challenge(c: &arena_types::ChallengeDefinition) -> Self {
        let r = &c.resource_limits;
        RunLimits {
            max_prepare_ms: r.max_prepare_ms,
            max_prove_ms: r.max_prove_ms.min(if c.measurement.per_run_timeout_ms > 0 {
                c.measurement.per_run_timeout_ms
            } else {
                u64::MAX
            }),
            max_verify_ms: r.max_verify_ms,
            max_ram_bytes: r.max_ram_bytes,
            max_proof_bytes: r.max_proof_bytes,
            max_claim_bytes: c.claim_encoding.max_claim_bytes,
            max_request_bytes: c.claim_encoding.max_request_bytes,
            max_witness_bytes: c.claim_encoding.max_witness_bytes,
            max_public_artifact_bytes: r.max_public_artifact_bytes,
            max_pids: 256,
            scratch_mb: 1024,
        }
    }
}

/// `PKG_WELLFORMED`: ingest the archive safely and validate `candidate.toml`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ValidateJob {
    /// Digest of the uploaded archive bytes (`tar` or `tar.zst`).
    pub package: Digest,
    pub challenge_id: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BuildLimits {
    pub max_build_ms: u64,
    pub mem_bytes: u64,
    pub pids: u32,
    pub scratch_mb: u64,
    pub max_output_bytes: u64,
}

/// `BUILD_REPRODUCIBLE`: run `build.recipe` offline in the sandbox twice in
/// fresh scratch dirs and compare output TreeDigests.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BuildJob {
    pub package: Digest,
    /// Pinned toolchain rootfs image (TreeDigest). `None` = the worker's
    /// configured dev toolchain (host-dev; recorded by digest of its
    /// description, DEMO-only).
    pub toolchain_image: Option<Digest>,
    pub limits: BuildLimits,
    pub source_date_epoch: u64,
}

/// `CONFORMANCE_DIFFERENTIAL` + `PROVER_RELIABILITY` (+ `RESOURCE_LIMITS`
/// observations): judge-run `prepare`, then per case `prove` (with witness)
/// and `verify` (in a separate sandbox with only public dir, claim, proof).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConformanceJob {
    /// Digest of the build bundle tar (as produced by the build job).
    pub bundle: Digest,
    pub entry: EntryPoints,
    /// `approved_params.bin`.
    pub params: Digest,
    pub cases: Vec<OracleCase>,
    pub limits: RunLimits,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HonestProof {
    pub case_id: String,
    pub claim: Digest,
    pub proof: Digest,
}

/// `ADVERSARIAL_PROOFS`: hostile (claim, proof) pairs derived from honest
/// proofs by pluggable mutators must all be rejected by `verify`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AdversarialJob {
    pub bundle: Digest,
    pub entry: EntryPoints,
    /// Tar of the frozen judge-run `public_dir`.
    pub public_artifacts: Digest,
    pub honest: Vec<HonestProof>,
    /// Mutator names to run; empty = every registered mutator.
    pub mutators: Vec<String>,
    pub seed: u64,
    pub limits: RunLimits,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BenchClass {
    pub class_id: String,
    pub weight_ppm: u32,
    pub baseline_ns: u64,
    /// The sampled batch (`batch_size` cases).
    pub batch: Vec<OracleCase>,
    /// Unseen batch for the fresh-confirm round (may be empty: no tripwire).
    pub fresh_batch: Vec<OracleCase>,
}

/// `BENCHMARK` (+ `RESOURCE_LIMITS`): trusted timing via `arena-measure`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BenchmarkJob {
    pub bundle: Digest,
    pub entry: EntryPoints,
    pub params: Digest,
    /// Frozen public dir to use for prove/verify; `prepare` is re-run once
    /// for timing either way.
    pub public_artifacts: Option<Digest>,
    pub classes: Vec<BenchClass>,
    pub procedure: MeasurementProcedure,
    pub hardware_profile: String,
    pub suite_revision: String,
    pub schedule_seed: u64,
    pub bootstrap_seed: u64,
    pub bootstrap_iterations: u32,
    pub limits: RunLimits,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NamedArtifact {
    /// e.g. `bundle`, `bundle_tree`, `public_artifacts`, `claim:<case>`.
    pub name: String,
    pub digest: Digest,
    /// Whether the artifact may be shown publicly (held-out data must not).
    pub public: bool,
    /// Whether the bytes were uploaded to the store (`false` for pure
    /// identifiers such as TreeDigests).
    pub stored: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SandboxInfo {
    pub backend: String,
    pub isolation: String,
    /// `Some(Demo)` when the backend is not production isolation: every gate
    /// in the output also carries reason code `DEMO_ONLY`.
    pub tier_cap: Option<arena_types::challenge::Tier>,
}

/// Result of executing a job.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JobOutput {
    pub job_id: String,
    pub gates: Vec<GateResult>,
    pub artifacts: Vec<NamedArtifact>,
    /// Validate jobs: the parsed manifest.
    pub manifest: Option<CandidateManifest>,
    pub benchmark: Option<BenchmarkResult>,
    pub sandbox: SandboxInfo,
    pub worker_id: String,
}

impl JobOutput {
    pub fn artifact(&self, name: &str) -> Option<&Digest> {
        self.artifacts
            .iter()
            .find(|a| a.name == name)
            .map(|a| &a.digest)
    }
}
