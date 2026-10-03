//! Backend-independent sandbox interface (CONTRACTS §9).

use arena_types::Digest;
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::time::Duration;

/// Guest path of the size-limited writable scratch tmpfs. `/tmp` is a
/// symlink to `/scratch/tmp`.
pub const SCRATCH: &str = "/scratch";

/// Default truncation for captured stdout / stderr (CONTRACTS §4).
pub const DEFAULT_OUTPUT_TRUNC: usize = 64 * 1024;

/// Environment variables a spec may set. Everything else is refused; the
/// sandbox always starts from an empty environment and adds
/// `PATH` (overridable), `HOME=/scratch`, `TMPDIR=/tmp`, `LANG=C.UTF-8`, `TZ=UTC` itself.
pub const ENV_ALLOWLIST: &[&str] = &[
    "SOURCE_DATE_EPOCH",
    "ARENA_STAGE",
    "CARGO_HOME",
    "CARGO_NET_OFFLINE",
    "CARGO_TARGET_DIR",
    "RUSTUP_HOME",
    "RUSTUP_TOOLCHAIN",
    "RUSTFLAGS",
    "RUST_BACKTRACE",
    "RUST_MIN_STACK",
    "LEAN_PATH",
    "ELAN_HOME",
    "PATH",
];

/// Guest prefixes under which read-only mounts may be placed (bwrap-dev).
pub const MOUNT_PREFIXES: &[&str] = &["/in/", "/opt/"];

/// Where a backend puts things inside the guest. Callers (the worker) build
/// argv / mounts from this instead of hard-coding paths, because backends
/// may differ (bwrap-dev and firecracker currently both use `/scratch`,
/// `/in`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GuestLayout {
    /// Writable scratch (cwd, `HOME`); `<scratch>/out` is always collectable.
    pub scratch: &'static str,
    /// Root for read-only input mounts (`<inputs>/bundle`, `<inputs>/public`, ...).
    pub inputs: &'static str,
    /// Allowed prefixes for read-only mounts.
    pub mount_prefixes: &'static [&'static str],
    /// Whether `copy_in` / `scratch_dirs` / a non-scratch `cwd` / arbitrary
    /// `collect` paths are supported. Backends without it only collect
    /// `out/**` and run in the scratch dir.
    pub flexible_scratch: bool,
}

pub const BWRAP_LAYOUT: GuestLayout =
    GuestLayout { scratch: SCRATCH, inputs: "/in", mount_prefixes: MOUNT_PREFIXES, flexible_scratch: true };

/// What the sandbox root filesystem is made of.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum Rootfs {
    /// The host's `/usr` (+ merged-usr symlinks and a few loader files from
    /// `/etc`), read-only. DEV ONLY: not a pinned image.
    HostDev,
    /// The backend's installed, pinned runtime image (firecracker: its
    /// verified rootfs; bwrap-dev: same as `HostDev`).
    BackendDefault,
    /// A directory holding an unpacked rootfs image whose TreeDigest is
    /// `digest`. Its top-level entries are bound read-only.
    Image { path: PathBuf, digest: Digest },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Mount {
    pub host: PathBuf,
    /// Absolute guest path under one of [`MOUNT_PREFIXES`].
    pub guest: String,
}

/// Copy a read-only guest path (file or directory) into scratch before the
/// entry point starts (e.g. a writable copy of the package for `build`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CopyIn {
    pub from_guest: String,
    /// Path relative to [`SCRATCH`].
    pub to_scratch: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Network {
    /// No network at all (a private network namespace with only `lo`).
    None,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SandboxSpec {
    pub rootfs: Rootfs,
    pub ro_mounts: Vec<Mount>,
    /// Size of the writable scratch tmpfs at [`SCRATCH`].
    pub rw_scratch_mb: u64,
    pub copy_in: Vec<CopyIn>,
    /// Scratch-relative directories created (after `copy_in`) before the
    /// entry point starts, e.g. an empty `--out` directory.
    pub scratch_dirs: Vec<String>,
    pub argv: Vec<String>,
    /// Absolute guest working directory (default [`SCRATCH`]).
    pub cwd: String,
    /// Extra environment; keys must be in [`ENV_ALLOWLIST`].
    pub env: Vec<(String, String)>,
    /// CPUs to run on. Placement is via affinity; the *amount* of CPU is
    /// enforced with `cpu.max` (= `len * 100%`) when cgroups are available.
    pub cpu_set: Option<Vec<u32>>,
    pub mem_bytes: u64,
    pub pids: u32,
    pub wall_timeout: Duration,
    pub network: Network,
    /// Scratch-relative paths (files or directories) to return after the
    /// entry point and every process it started have exited.
    pub collect: Vec<String>,
    /// Host directory (must not exist) receiving collected outputs.
    pub out_dir: Option<PathBuf>,
    pub max_output_bytes: u64,
    pub output_trunc_bytes: usize,
}

impl SandboxSpec {
    /// A spec with conservative defaults: host-dev rootfs, 64 MiB scratch,
    /// 512 MiB RAM, 64 pids, 60 s.
    pub fn new(argv: Vec<String>) -> Self {
        SandboxSpec {
            rootfs: Rootfs::BackendDefault,
            ro_mounts: vec![],
            rw_scratch_mb: 64,
            copy_in: vec![],
            scratch_dirs: vec![],
            argv,
            cwd: SCRATCH.to_string(),
            env: vec![],
            cpu_set: None,
            mem_bytes: 512 << 20,
            pids: 64,
            wall_timeout: Duration::from_secs(60),
            network: Network::None,
            collect: vec![],
            out_dir: None,
            max_output_bytes: 256 << 20,
            output_trunc_bytes: DEFAULT_OUTPUT_TRUNC,
        }
    }

    /// Structural validation shared by all backends.
    pub fn validate(&self) -> Result<(), InfraError> {
        self.validate_for(&BWRAP_LAYOUT)
    }

    /// Structural validation against a backend's guest layout.
    pub fn validate_for(&self, layout: &GuestLayout) -> Result<(), InfraError> {
        let bad = |s: String| Err(InfraError::InvalidSpec(s));
        if self.argv.is_empty() || self.argv.iter().any(|a| a.contains('\0')) {
            return bad("argv must be non-empty and NUL-free".into());
        }
        for (k, v) in &self.env {
            if !ENV_ALLOWLIST.contains(&k.as_str()) {
                return bad(format!("env var {k:?} not in allowlist"));
            }
            if v.contains('\0') {
                return bad(format!("env var {k:?} contains NUL"));
            }
        }
        for m in &self.ro_mounts {
            check_guest_path(&m.guest)?;
            if !layout.mount_prefixes.iter().any(|p| m.guest.starts_with(p)) {
                return bad(format!("mount {:?} not under {:?}", m.guest, layout.mount_prefixes));
            }
            if !m.host.is_absolute() {
                return bad(format!("mount host path {:?} must be absolute", m.host));
            }
        }
        for c in &self.copy_in {
            check_guest_path(&c.from_guest)?;
            arena_archive::path::check_relpath(&c.to_scratch).map_err(InfraError::InvalidSpec)?;
        }
        for c in self.collect.iter().chain(&self.scratch_dirs) {
            arena_archive::path::check_relpath(c).map_err(InfraError::InvalidSpec)?;
        }
        check_guest_path(&self.cwd)?;
        if self.rw_scratch_mb == 0 || self.mem_bytes < (16 << 20) || self.pids < 4 {
            return bad("scratch/mem/pids limits too small".into());
        }
        if self.wall_timeout.is_zero() {
            return bad("zero wall timeout".into());
        }
        if !self.collect.is_empty() && self.out_dir.is_none() {
            return bad("collect requires out_dir".into());
        }
        if !layout.flexible_scratch {
            if !self.copy_in.is_empty() || !self.scratch_dirs.is_empty() {
                return bad("copy_in / scratch_dirs not supported by this backend".into());
            }
            if self.cwd != layout.scratch {
                return bad(format!("cwd must be {}", layout.scratch));
            }
            if !self.collect.iter().all(|c| c == "out" || c.starts_with("out/")) {
                return bad("this backend only collects paths under out/".into());
            }
        }
        if let Some(cpus) = &self.cpu_set {
            if cpus.is_empty() || cpus.iter().any(|&c| c >= 1024) {
                return bad("bad cpu_set".into());
            }
        }
        Ok(())
    }
}

fn check_guest_path(p: &str) -> Result<(), InfraError> {
    let rel = p
        .strip_prefix('/')
        .ok_or_else(|| InfraError::InvalidSpec(format!("guest path {p:?} must be absolute")))?;
    if rel.is_empty() {
        return Ok(());
    }
    arena_archive::path::check_relpath(rel).map_err(InfraError::InvalidSpec)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "kind", content = "value")]
pub enum ExitStatus {
    /// Entry point exited with this code.
    Exited(i32),
    /// Entry point was killed by this signal (not by the supervisor).
    Signaled(i32),
    /// Supervisor killed the sandbox at `wall_timeout`.
    TimedOut,
    /// The kernel OOM killer fired inside the sandbox's memory cgroup.
    OomKilled,
    /// The entry point could not be executed (missing, not executable, bad
    /// interpreter, ...). Candidate-caused.
    ExecFailed,
}

impl ExitStatus {
    pub fn success(self) -> bool {
        self == ExitStatus::Exited(0)
    }
}

/// How resource limits were enforced for a run.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum LimitEnforcement {
    /// Transient delegated cgroup v2 (memory.max, pids.max, cpu.max, oom.group).
    CgroupV2,
    /// setrlimit fallback (RLIMIT_AS, RLIMIT_NPROC) — weaker.
    Rlimit,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SandboxOutcome {
    pub exit: ExitStatus,
    /// Supervisor-measured wall time (host monotonic clock, around the whole
    /// sandbox lifetime).
    pub wall_ns: u64,
    /// CPU time of everything in the sandbox (cgroup `cpu.stat` or rusage).
    pub cpu_ns: u64,
    /// cgroup `memory.peak` when available, else max per-process RSS.
    pub peak_rss_bytes: u64,
    /// Max RSS of any single process (rusage), always reported.
    pub max_process_rss_bytes: u64,
    pub stdout_trunc: Vec<u8>,
    pub stderr_trunc: Vec<u8>,
    pub stdout_bytes: u64,
    pub stderr_bytes: u64,
    /// Collected files as (scratch-relative path, digest), sorted by path.
    pub outputs: Vec<(String, Digest)>,
    /// TreeDigest of everything collected.
    pub outputs_tree: Option<Digest>,
    /// Set when collected outputs were unsafe or over the size limit; the
    /// outputs are then empty. Candidate-caused.
    pub output_error: Option<String>,
    pub pids_limit_hit: bool,
    pub limits: LimitEnforcement,
    /// Backend label; results produced through `bwrap-dev` are tier-capped
    /// at `demo`.
    pub isolation: String,
    pub tier_cap: Option<arena_types::challenge::Tier>,
    /// Diagnostic: entry-point-only wall time measured by the judge's init
    /// inside the sandbox. Never used for scoring.
    pub entry_wall_ns: Option<u64>,
    /// Backend-specific, non-authoritative detail.
    pub diagnostics: Diagnostics,
}

impl SandboxOutcome {
    /// An outcome with every measurement zeroed; backends fill in fields.
    pub fn empty(exit: ExitStatus, isolation: &str, tier_cap: Option<arena_types::challenge::Tier>) -> Self {
        SandboxOutcome {
            exit,
            wall_ns: 0,
            cpu_ns: 0,
            peak_rss_bytes: 0,
            max_process_rss_bytes: 0,
            stdout_trunc: vec![],
            stderr_trunc: vec![],
            stdout_bytes: 0,
            stderr_bytes: 0,
            outputs: vec![],
            outputs_tree: None,
            output_error: None,
            pids_limit_hit: false,
            limits: LimitEnforcement::CgroupV2,
            isolation: isolation.to_string(),
            tier_cap,
            entry_wall_ns: None,
            diagnostics: Diagnostics::default(),
        }
    }
}

/// Backend detail; nothing here is used for decisions (except the
/// benchmark harness's host/VMM wall-time cross-check).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostics {
    pub backend: String,
    /// Host: whole run including setup/teardown.
    pub total_ns: u64,
    /// firecracker: jailer spawn -> guest start marker.
    pub boot_ns: Option<u64>,
    /// firecracker: jailer spawn -> Firecracker exit (0 if not applicable).
    pub vmm_wall_ns: u64,
    /// firecracker: guest exit marker -> Firecracker exit.
    pub teardown_ns: Option<u64>,
    /// Guest-side (diagnostic) figures.
    pub guest_wall_ns: Option<u64>,
    pub guest_cpu_ns: Option<u64>,
    pub guest_peak_mem_bytes: Option<u64>,
    pub stdout_total_bytes: Option<u64>,
    pub stderr_total_bytes: Option<u64>,
    /// Host cgroup OOM kills of the VMM.
    pub host_oom_kills: u64,
    /// Output-collection policy violations (symlinks, limits, ...).
    pub output_violations: Vec<String>,
    pub outputs_complete: bool,
    /// Tail of the serial console / supervisor stderr, for debugging.
    pub serial_tail: String,
}

/// Compatibility alias (the firecracker backend's original name).
pub type Exit = ExitStatus;

#[derive(Debug, thiserror::Error)]
pub enum InfraError {
    #[error("sandbox backend refused: {0}")]
    Refused(String),
    #[error("invalid sandbox spec: {0}")]
    InvalidSpec(String),
    #[error("sandbox spawn failed: {0}")]
    Spawn(String),
    #[error("sandbox supervisor: {0}")]
    Supervisor(String),
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
    #[error("sandbox backend unavailable: {0}")]
    Unavailable(String),
    #[error("sandbox infrastructure failure: {0}")]
    Backend(String),
    /// The guest produced a malformed or forged report. Only possible if the
    /// candidate compromised the guest's judge side (or init is buggy): maps
    /// to `SANDBOX_VIOLATION`, not to a retryable infra error.
    #[error("guest protocol violation: {0}")]
    GuestProtocol(String),
}

/// A sandbox backend. Implementations run untrusted code with no network,
/// read-only inputs, size-limited scratch, and enforced resource limits, and
/// measure everything from outside the sandbox.
pub trait Sandbox: Send + Sync {
    /// Short backend id, e.g. `bwrap-dev`, `firecracker`.
    fn name(&self) -> &str;
    /// Tier cap that every result produced through this backend carries
    /// (`Some(Demo)` for dev backends, `None` for production isolation).
    fn tier_cap(&self) -> Option<arena_types::challenge::Tier>;
    /// Guest path layout (defaults to the bwrap-dev layout).
    fn layout(&self) -> GuestLayout {
        BWRAP_LAYOUT
    }
    fn run(&self, spec: &SandboxSpec) -> Result<SandboxOutcome, InfraError>;
}
