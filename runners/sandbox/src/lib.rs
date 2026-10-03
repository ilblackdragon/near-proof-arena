//! Sandbox interface (CONTRACTS §9) and the `bwrap-dev` backend.
//!
//! Untrusted candidate code runs **only** through [`Sandbox::run`]. The
//! production backend (`firecracker`, microVM) lives in `runners/firecracker`
//! and implements the same trait; `bwrap-dev` is a namespaces-only
//! development backend whose results are always tier-capped at `demo`.

pub mod bwrap;
pub mod helper;
pub mod spec;

pub use bwrap::{BwrapConfig, BwrapDev, CgroupMode, HelperCommand, ISOLATION_LABEL};
pub use spec::*;
