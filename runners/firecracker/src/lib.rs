//! Firecracker microVM backend for the arena `Sandbox` contract
//! (docs/CONTRACTS.md §9, docs/ISOLATION.md).
//!
//! Layering, outermost first:
//!
//! 1. host library (this crate, unprivileged host user): validates the spec,
//!    builds fresh per-run disk images, starts the delivery container, applies
//!    a backstop deadline, decodes the guest's raw output device;
//! 2. delivery container (`arena-fc-runner` image: firecracker, jailer,
//!    `arena-fc-shim` only): `--network none`, minimal capabilities, Docker
//!    seccomp + pivot_root, read-only rootfs, memory/pids limits;
//! 3. jailer: chroot (pivot_root), per-run unprivileged uid/gid, cgroup v2
//!    limits, rlimits; Firecracker with its default seccomp filters;
//! 4. **the microVM** (the security boundary): no network device, no vsock,
//!    only virtio-blk drives (rootfs ro, control ro, bundles ro, scratch rw,
//!    output rw) and the serial console;
//! 5. guest `arena-init`: candidate runs as uid 1000 with a cleared env, in a
//!    memory/pids-limited cgroup, with rlimits and no_new_privs.

pub mod contract;
pub mod images;
pub mod sandbox;

pub use contract::{Diagnostics, Exit, InfraError, NetworkAccess, RoMount, Sandbox, SandboxOutcome, SandboxSpec};
pub use sandbox::{FirecrackerConfig, FirecrackerSandbox, CONTAINER_CAPS, ENV_ALLOWLIST};
