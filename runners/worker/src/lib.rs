//! Arena judge worker (CONTRACTS §9).
//!
//! `arena-worker` leases a job from the control plane, fetches its inputs by
//! digest, runs candidate code only through an [`arena_sandbox::Sandbox`],
//! uploads outputs by digest and completes the job with [`jobs::JobOutput`]
//! (gate results + artifact digests). It never holds database credentials.
//!
//! Seams for other lanes:
//! * [`jobs`] — plain job payload structs mirroring CONTRACTS; the server
//!   lane's `server/arena-jobs` types map onto them.
//! * [`executor::JobExecutor`] — job semantics behind a trait.
//! * [`client::ControlPlane`] / [`store::ArtifactStore`] — transport.
//! * [`mutators::ProofMutator`] — hostile proof generators (adversarial lane).

pub mod client;
pub mod config;
pub mod daemon;
pub mod executor;
pub mod gate;
pub mod jobs;
pub mod mutators;
pub mod stages;
pub mod store;

/// argv[1] that turns the `arena-worker` binary into the sandbox helper
/// (so a single binary can be deployed).
pub const HELPER_ARG: &str = "__arena-sandbox-helper";
