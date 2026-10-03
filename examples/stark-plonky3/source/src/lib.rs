//! `stark-plonky3`: a custom Plonky3 STARK for
//! `near/pv86/receipt-transfer-batch/v0` (hand-written AIRs, see `air/`).

pub mod air;
pub mod colnames;
pub mod config;
pub mod consts;
pub mod engine;
pub mod spec;
pub mod trie;
pub mod wire;

pub use sha2::{Digest as _, Sha256};

/// SHA-256 of `b`.
#[inline]
pub fn sha256(b: &[u8]) -> [u8; 32] {
    use sha2::Digest;
    Sha256::digest(b).into()
}
pub mod eval;
pub mod fingerprint;
pub mod proof;
pub mod security;
pub mod trace;
pub mod witness;

/// Parse `--flag value` pairs; exits with code 2 on malformed argv.
pub fn parse_args(expected: &[&str]) -> std::collections::BTreeMap<String, std::path::PathBuf> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut out = std::collections::BTreeMap::new();
    let mut it = args.into_iter();
    while let Some(flag) = it.next() {
        let Some(name) = flag.strip_prefix("--") else { die(&format!("unexpected argument {flag}")) };
        if !expected.contains(&name) {
            die(&format!("unknown flag --{name}"));
        }
        let Some(v) = it.next() else { die(&format!("--{name} needs a value")) };
        if out.insert(name.to_string(), std::path::PathBuf::from(v)).is_some() {
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
