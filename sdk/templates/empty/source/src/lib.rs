//! Shared helpers for the three entry points.
//!
//! Process interface (docs/AGENT_CONTRACT.md §4):
//!
//! ```text
//! prepare --params <approved_params.bin> --out <public_dir>
//! prove   --public <public_dir> --request <request.bin> --witness <witness.bin>
//!         --claim-out <claim.bin> --proof-out <proof.bin>
//! verify  --public <public_dir> --claim <claim.bin> --proof <proof.bin>
//! ```
//!
//! Exit codes: 0 = success / accept, 1 = reject (verify only), anything else
//! (including panics, signals, timeouts) = error. An error is never "accept".

use std::collections::BTreeMap;
use std::path::PathBuf;

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
        out.insert(name.to_string(), PathBuf::from(v));
    }
    for e in expected {
        if !out.contains_key(*e) {
            die(&format!("missing --{e}"));
        }
    }
    out
}

/// Exit with an *error* (code 2). Never use this to mean "reject".
pub fn die(msg: &str) -> ! {
    eprintln!("error: {msg}");
    std::process::exit(2)
}
