//! `reexec-witness` reference backend for `near/pv86/receipt-transfer-batch/v0`.
//!
//! The proof is the canonical encoding of an authenticated witness: the
//! ordered receipt batch (nearcore borsh, byte-identical to the request) and
//! the partial pre-state trie that the batch touches. Verification decodes the
//! claim and the proof and re-executes the NEAR relation
//! (`NearSpec.TransferV1.NearRelation`). The deployed verifier is the Lean
//! model `ReexecWitness.Model.verifier` compiled by the governed Lean compiler;
//! the Rust re-checker in [`check`] is a test oracle only.
//!
//! Process interface: `docs/AGENT_CONTRACT.md` §5. Encodings:
//! `spec/claim-v1.md`, proof format: `README.md` of this package and
//! `formal/ReexecWitness/ProofCodec.lean` (the Lean encoder is normative).

pub mod check;
pub mod engine;
pub mod proof;
pub mod spec;
pub mod trie;
pub mod wire;

use std::collections::BTreeMap;
use std::path::PathBuf;

pub use sha2::{Digest as _, Sha256};

/// SHA-256 of `b`.
#[inline]
pub fn sha256(b: &[u8]) -> [u8; 32] {
    Sha256::digest(b).into()
}

/// Parse `--flag value` pairs; exits with code 2 on malformed argv.
pub fn parse_args(expected: &[&str]) -> BTreeMap<String, PathBuf> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut out = BTreeMap::new();
    let mut it = args.into_iter();
    while let Some(flag) = it.next() {
        let Some(name) = flag.strip_prefix("--") else { die(&format!("unexpected argument {flag}")) };
        if !expected.contains(&name) {
            die(&format!("unknown flag --{name}"));
        }
        let Some(v) = it.next() else { die(&format!("--{name} needs a value")) };
        if out.insert(name.to_string(), PathBuf::from(v)).is_some() {
            die(&format!("duplicate flag --{name}"));
        }
    }
    for e in expected {
        if !out.contains_key(*e) {
            die(&format!("missing --{e}"));
        }
    }
    out
}

/// Exit with an *error* (code 2). Never used to mean "reject".
pub fn die(msg: &str) -> ! {
    eprintln!("error: {msg}");
    std::process::exit(2)
}
