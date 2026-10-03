//! Native request type of the Firecracker backend.
//!
//! The shared runner contract (`Sandbox`, `SandboxSpec`, `SandboxOutcome`,
//! `Exit`, `Diagnostics`, `InfraError`) lives in `runners/sandbox`
//! (`arena-sandbox`); `FirecrackerSandbox` implements `arena_sandbox::Sandbox`
//! by translating a `SandboxSpec` into the [`RunRequest`] below (the
//! backend-level form used by the operator CLI and the VM tests).

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
pub struct RunRequest {
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
    /// Host directory receiving output files; must be empty or absent.
    pub out_dir: PathBuf,
    /// Cap on collected output bytes (also bounded by the backend config
    /// and the scratch size).
    pub max_output_bytes: u64,
}

