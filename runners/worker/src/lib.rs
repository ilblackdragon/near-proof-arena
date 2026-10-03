//! Arena judge worker (CONTRACTS §9).
//!
//! `arena-worker` leases a job from the control plane, fetches its inputs by
//! digest, runs candidate code only through an [`arena_sandbox::Sandbox`],
//! uploads outputs by digest and completes the job with an
//! `arena_jobs::JobResult` (gate results + artifact digests). It never holds
//! database credentials.
//!
//! Seams:
//! * job / result / wire types: `server/arena-jobs` (single source).
//! * [`executor::JobExecutor`] — job semantics behind a trait.
//! * [`control::ControlPlane`] / [`store::ArtifactStore`] — transport.
//! * [`oracle::Oracle`] — expected claims and workload sampling per claim
//!   encoding (spec-oracle lane).
//! * [`mutators::ProofMutator`] — hostile proof generators (adversarial lane).

pub mod config;
pub mod control;
pub mod daemon;
pub mod executor;
pub mod gate;
pub mod jobs;
pub mod mutators;
pub mod oracle;
pub mod stages;
pub mod store;

/// argv[1] that turns the `arena-worker` binary into the sandbox helper
/// (so a single binary can be deployed).
pub const HELPER_ARG: &str = "__arena-sandbox-helper";
