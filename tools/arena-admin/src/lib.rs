//! Governance tooling for NEAR Proof Arena (`tools/arena-admin`).
//!
//! The library is usable by the server to verify challenge files with the
//! exact same rules the CLI enforces when signing.

pub mod challenge_file;
pub mod governed;
pub mod keys;
pub mod policy;

pub use challenge_file::{verify_file, Verified};
pub use governed::GovernedSet;
pub use keys::{Keypair, PublicKey};
