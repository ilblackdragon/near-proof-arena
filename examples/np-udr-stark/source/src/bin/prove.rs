//! `prove --public <dir> --request <request.bin> --witness <witness.bin>
//!        --claim-out <claim.bin> --proof-out <proof.bin>`
//!
//! Judge entry point (docs/CONTRACTS.md §4):
//! 1. decode `request.bin` / `witness.bin` and derive the claim (`claim.bin`
//!    = `encodeClaim c`, the reexec engine = NearSpec `deriveClaim`);
//! 2. build the honest `nearAir` trace (`npudr::near`, a cell-for-cell port of
//!    lane L6's `Near.render (extOf c w)` plus L5's SHA table);
//! 3. prove `np-udr-stark-v1` with the public tape `public.bin` and claim
//!    bytes `cb = claim.bin` (FORMATS.md §4) and write both files.
//! Any failure exits 2 and writes nothing (an error is never an accept).
//! `NPUDR_VERBOSE=1` prints per-phase timings on stderr.
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
    let pub_tape = std::fs::read(a["public"].join("public.bin")).unwrap_or_else(|e| die(&format!("public: {e}")));
    let req = std::fs::read(&a["request"]).unwrap_or_else(|e| die(&format!("request: {e}")));
    let wit = std::fs::read(&a["witness"]).unwrap_or_else(|e| die(&format!("witness: {e}")));
    let verbose = std::env::var("NPUDR_VERBOSE").is_ok_and(|v| v == "1");
    let t0 = std::time::Instant::now();
    let (claim, air, traces) = npudr::near::prepare(&req, &wit).unwrap_or_else(|e| die(&e));
    if verbose {
        let shapes: Vec<String> = traces.iter().map(|m| format!("{}x{}", m.width, m.values.len() / m.width.max(1))).collect();
        eprintln!("[prove] trace {:.3}s tables {}", t0.elapsed().as_secs_f64(), shapes.join(" "));
    }
    let opts = npudr::prover::ProveOptions { verbose };
    let proof = npudr::prover::prove_bytes(&air, traces, &pub_tape, &claim, &opts).unwrap_or_else(|e| die(&e));
    if verbose {
        eprintln!("[prove] total {:.3}s proof {} B", t0.elapsed().as_secs_f64(), proof.len());
    }
    std::fs::write(&a["claim-out"], &claim).unwrap_or_else(|e| die(&format!("claim-out: {e}")));
    std::fs::write(&a["proof-out"], &proof).unwrap_or_else(|e| die(&format!("proof-out: {e}")));
}
