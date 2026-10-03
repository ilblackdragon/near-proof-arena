//! Local copy of the runner `Sandbox` contract (docs/CONTRACTS.md §9).
//!
//! INTEGRATOR NOTE: the shared definition lives in `runners/sandbox`
//! (runners-core lane), which was being written concurrently with this
//! crate. Once it lands, delete this module and `impl
//! arena_sandbox::Sandbox for FirecrackerSandbox` instead; the field names
//! below follow §9 one-to-one. Deliberate deviations, all additive, that the
//! shared crate needs to either adopt or map:
//!
//! * `SandboxSpec::out_dir` — host directory into which output files are
//!   materialized (§9 lists `outputs: [(path, Digest)]` but not where the
//!   bytes go).
//! * `Exit::Signaled(i32)` carries the signal number.
//! * `SandboxOutcome::diagnostics` — backend-specific, non-authoritative
//!   detail (boot latency, guest-side figures, output-policy violations).
//! * `InfraError` distinguishes `GuestProtocol` (the guest wrote a malformed
//!   report: only possible if the candidate compromised guest root or init
//!   is buggy; map to `SANDBOX_VIOLATION`) from ordinary infra failures.

use arena_types::Digest;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::time::Duration;

/// A host directory or single file exposed read-only to the candidate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoMount {
    pub host_path: PathBuf,
    /// Absolute guest path; for this backend it must be under `/arena/`
    /// (the guest rootfs is read-only) and must not overlap the scratch dir
    /// `/arena/scratch`.
    pub guest_path: String,
}

/// Network access is not offered by any backend; the only legal value of
/// `SandboxSpec::network` is `None`. This type is uninhabited on purpose.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NetworkAccess {}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SandboxSpec {
    /// Digest of the guest root filesystem image the run must use.
    pub rootfs_digest: Digest,
    pub ro_mounts: Vec<RoMount>,
    /// Size of the fresh per-run scratch disk mounted at `/arena/scratch`
    /// (also the cwd). Files left under `/arena/scratch/out` are outputs.
    pub rw_scratch_mb: u64,
    pub argv: Vec<String>,
    /// Must only use names from the backend's fixed allowlist.
    pub env: Vec<(String, String)>,
    /// Host CPUs the VM is pinned to; vCPU count = `cpu_set.len()` (1 if empty).
    pub cpu_set: Vec<u32>,
    /// Memory available to the candidate's processes (guest cgroup limit).
    pub mem_bytes: u64,
    pub pids: u32,
    pub wall_timeout: Duration,
    pub network: Option<NetworkAccess>,
    /// (addition) Host directory receiving output files; must be empty or absent.
    pub out_dir: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Exit {
    Exited(i32),
    Signaled(i32),
    TimedOut,
    OomKilled,
}

/// Backend detail; nothing here is used for decisions.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostics {
    pub backend: String,
    /// Host: container start request -> container exit.
    pub total_ns: u64,
    /// Host: jailer spawn -> guest start marker on the serial console.
    pub boot_ns: Option<u64>,
    /// Host: jailer spawn -> Firecracker exit.
    pub vmm_wall_ns: u64,
    /// Host: guest exit marker -> Firecracker exit (output collection).
    pub teardown_ns: Option<u64>,
    /// Guest (diagnostic): candidate cgroup figures reported by arena-init.
    pub guest_wall_ns: Option<u64>,
    pub guest_cpu_ns: Option<u64>,
    pub guest_peak_mem_bytes: Option<u64>,
    pub stdout_total_bytes: Option<u64>,
    pub stderr_total_bytes: Option<u64>,
    /// Host cgroup OOM kills of the VMM (guest RAM + VMM overhead).
    pub host_oom_kills: u64,
    /// Output-collection policy violations (symlinks, limits, ...).
    pub output_violations: Vec<String>,
    pub outputs_complete: bool,
    /// Tail of the serial console (kernel + init messages), for debugging.
    pub serial_tail: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SandboxOutcome {
    pub exit: Exit,
    /// Candidate wall time measured on the host clock: guest start marker
    /// -> guest exit marker (or -> kill on timeout). Excludes VM boot.
    pub wall_ns: u64,
    /// Host cgroup CPU time of the whole VMM (vCPUs + device emulation),
    /// including guest boot/teardown. Authoritative.
    pub cpu_ns: u64,
    /// Host cgroup `memory.peak` of the VMM (guest RAM actually touched +
    /// VMM overhead). Authoritative upper bound; the per-candidate limit is
    /// enforced inside the guest (see diagnostics for the guest figure).
    pub peak_rss_bytes: u64,
    pub stdout_trunc: Vec<u8>,
    pub stderr_trunc: Vec<u8>,
    /// Relative paths under the output dir and their content digests.
    pub outputs: Vec<(String, Digest)>,
    pub diagnostics: Diagnostics,
}

#[derive(Debug, thiserror::Error)]
pub enum InfraError {
    #[error("invalid sandbox spec: {0}")]
    InvalidSpec(String),
    #[error("sandbox backend unavailable: {0}")]
    Unavailable(String),
    #[error("i/o: {0}")]
    Io(#[from] std::io::Error),
    #[error("sandbox infrastructure failure: {0}")]
    Backend(String),
    /// The guest produced a malformed/forged report.
    #[error("guest protocol violation: {0}")]
    GuestProtocol(String),
}

pub trait Sandbox {
    fn run(&self, spec: &SandboxSpec) -> Result<SandboxOutcome, InfraError>;
}
