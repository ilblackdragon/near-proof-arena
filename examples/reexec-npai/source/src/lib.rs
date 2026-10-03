//! `reexec-npai` prover for `near/pv86/receipt-transfer-batch/v0`.
//!
//! The proof carries the authenticated witness (the receipt batch, nearcore
//! borsh, byte-identical to the request, and the partial pre-state trie) in
//! the bytecode-friendly layout `reexec-npai-v1` (post-order trie records with
//! raw node preimages). The deployed verifier is NPAI bytecode
//! (`formal/ReexecNpai/Program.lean`) executed by the arena's interpreter.
//!
//! Process interface: `docs/AGENT_CONTRACT.md` §5. Encodings:
//! `spec/claim-v1.md`; proof format: `formal/ReexecNpai/Codec.lean`
//! (`encodeProof`, normative).

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
