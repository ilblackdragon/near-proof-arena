//! Native request type of the Firecracker backend.
//!
//! The shared runner contract (`Sandbox`, `SandboxSpec`, `SandboxOutcome`,
//! `Exit`, `Diagnostics`, `InfraError`) lives in `runners/sandbox`
//! (`arena-sandbox`); `FirecrackerSandbox` implements `arena_sandbox::Sandbox`
//! by translating a `SandboxSpec` into the [`RunRequest`] below (the
//! backend-level form used by the operator CLI and the VM tests).
//!
//! Guest layout (identical to bwrap-dev): scratch disk at `/scratch` (cwd
//! by default, `HOME`, `/tmp` lives on it), read-only inputs under `/in/` and
//! `/opt/`.

use arena_types::Digest;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::time::Duration;

/// A host directory or single file exposed read-only to the candidate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoMount {
    pub host_path: PathBuf,
    /// Absolute guest path under `/in/` or `/opt/`, not overlapping scratch
    /// or another mount.
    pub guest_path: String,
}

/// An alternative candidate root filesystem (e.g. a pinned build toolchain):
/// a host directory whose `arena_archive` TreeDigest is `digest`. The arena
/// rootfs still boots the VM and runs init; the candidate is chrooted into a
/// read-only view of this image.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RootImage {
    pub dir: PathBuf,
    pub digest: Digest,
}

/// A host directory exposed read-write at `guest_path`: its current content
/// (judge-planted symlinks allowed) seeds the guest copy; afterwards the
/// regular files the guest left there are written back (new files created,
/// existing regular files replaced; host symlinks are never followed;
/// deletions are not propagated).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RwDir {
    pub host_dir: PathBuf,
    pub guest_path: String,
}

/// Network access is not offered by any backend; the only legal value of
/// `network` is `None`. This type is uninhabited on purpose.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum NetworkAccess {}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunRequest {
    /// Digest of the arena guest rootfs the run must boot (must equal the
    /// installed one).
    pub rootfs_digest: Digest,
    /// Candidate root; `None` = the arena rootfs.
    pub root_image: Option<RootImage>,
    pub ro_mounts: Vec<RoMount>,
    /// Read-write host directories (judge-owned outputs, e.g. `.olean`s).
    pub rw_dirs: Vec<RwDir>,
    /// Copy symlinks in read-only mount trees verbatim (they resolve inside
    /// the guest) instead of refusing them. Only for judge-built layouts such
    /// as the formal checker's olean link farms; never for candidate trees.
    pub allow_mount_symlinks: bool,
    /// Size of the fresh per-run scratch disk mounted at `/scratch`.
    pub rw_scratch_mb: u64,
    /// `(absolute guest path, scratch-relative destination)` copied into
    /// scratch before the entry point starts (owned by the candidate).
    pub copy_in: Vec<(String, String)>,
    /// Scratch-relative directories created after `copy_in`.
    pub scratch_dirs: Vec<String>,
    pub argv: Vec<String>,
    /// Absolute guest working directory.
    pub cwd: String,
    /// Must only use names from the allowlists.
    pub env: Vec<(String, String)>,
    /// Host CPUs the VM is pinned to; vCPU count = `cpu_set.len()` (1 if empty).
    pub cpu_set: Vec<u32>,
    /// Memory available to the candidate's processes (guest cgroup limit).
    pub mem_bytes: u64,
    pub pids: u32,
    pub wall_timeout: Duration,
    pub network: Option<NetworkAccess>,
    /// Scratch-relative files/directories collected after the run.
    pub collect: Vec<String>,
    /// Host directory receiving collected files at their scratch-relative
    /// paths; must be empty or absent.
    pub out_dir: PathBuf,
    /// Cap on collected output bytes (also bounded by the backend config
    /// and the scratch size).
    pub max_output_bytes: u64,
    /// Steps mode (non-empty): run these in order in this one VM instead of
    /// `argv`/`collect` (which must then be empty); `wall_timeout` must be
    /// the sum of the step timeouts. See `arena_fc_proto::GuestJob::steps`.
    #[serde(default)]
    pub steps: Vec<NativeStep>,
    /// Seccomp violation detection for the candidate tree (`Strict` for
    /// entry points, `Tooling` for builds/judge tools, `Off`).
    #[serde(default)]
    pub syscall_policy: arena_seccomp::Policy,
}

/// One step of a steps-mode run.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeStep {
    pub argv: Vec<String>,
    /// Single host files exposed read-only at the guest path, this step only.
    pub ro_files: Vec<RoMount>,
    /// Scratch-relative paths collected after the step; materialized at
    /// `out_dir/.step<i>/<path>`.
    pub collect: Vec<String>,
    pub wall_timeout: Duration,
}

impl RunRequest {
    /// Defaults for the CLI/tests: arena rootfs, 64 MiB scratch with an empty
    /// `out/` collected, cwd `/scratch`, 256 MiB, 64 pids, 60 s.
    pub fn new(rootfs_digest: Digest, argv: Vec<String>, out_dir: PathBuf) -> Self {
        RunRequest {
            rootfs_digest,
            root_image: None,
            ro_mounts: vec![],
            rw_dirs: vec![],
            allow_mount_symlinks: false,
            rw_scratch_mb: 64,
            copy_in: vec![],
            scratch_dirs: vec!["out".into()],
            argv,
            cwd: arena_fc_proto::GUEST_SCRATCH.into(),
            env: vec![],
            cpu_set: vec![],
            mem_bytes: 256 << 20,
            pids: 64,
            wall_timeout: Duration::from_secs(60),
            network: None,
            collect: vec!["out".into()],
            out_dir,
            max_output_bytes: 1 << 30,
            steps: vec![],
            syscall_policy: arena_seccomp::Policy::Strict,
        }
    }
}
