//! `prove --public <dir> --request <request.bin> --witness <witness.bin>
//!        --claim-out <claim.bin> --proof-out <proof.bin>`
//!
//! Judge entry point (docs/CONTRACTS.md §4). STUB: the protocol engine
//! (`npudr::prover`) exists, but the NEAR AIR (lane L6, `nearAir` exported by
//! the Lean AIR DSL) and the witness → trace generation do not yet. Until
//! they land this binary validates its CLI and inputs, then fails with exit
//! code 2 and writes nothing (an error is never an accept).
use std::collections::BTreeMap;
use std::path::PathBuf;

fn die(msg: &str) -> ! {
    eprintln!("error: {msg}");
    std::process::exit(2)
}

/// `--flag value` pairs; every expected flag exactly once, nothing else.
/// (Same conventions as examples/reexec-witness `parse_args`.)
fn parse_args(expected: &[&str]) -> BTreeMap<String, PathBuf> {
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

fn main() {
    let a = parse_args(&["public", "request", "witness", "claim-out", "proof-out"]);
    std::fs::read(a["public"].join("public.bin")).unwrap_or_else(|e| die(&format!("public: {e}")));
    std::fs::read(&a["request"]).unwrap_or_else(|e| die(&format!("request: {e}")));
    std::fs::read(&a["witness"]).unwrap_or_else(|e| die(&format!("witness: {e}")));
    die("not yet implemented: NEAR AIR pending (L6); np-udr-stark-v1 cannot prove NearRelation yet")
}
