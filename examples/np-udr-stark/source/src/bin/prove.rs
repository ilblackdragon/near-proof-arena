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
//! Any failure exits 2 and writes nothing (an error is never an accept):
//! malformed / out-of-domain inputs are `Err`s of `npudr::near::prepare`, and
//! as a backstop the whole computation runs under `catch_unwind` (release
//! profile: `panic = "unwind"`) on a big-stack thread; the outputs are written
//! only after success, each to a temporary file renamed into place.
//! `NPUDR_VERBOSE=1` prints per-phase timings on stderr.
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

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

/// Write `bytes` to `<path>.tmp-<pid>`; returns the temporary path.
fn write_tmp(path: &Path, bytes: &[u8]) -> Result<PathBuf, String> {
    let mut name = path.file_name().ok_or_else(|| format!("{}: not a file path", path.display()))?.to_os_string();
    name.push(format!(".tmp-{}", std::process::id()));
    let tmp = path.with_file_name(name);
    std::fs::write(&tmp, bytes).map_err(|e| {
        let _ = std::fs::remove_file(&tmp);
        format!("{}: {e}", path.display())
    })?;
    Ok(tmp)
}

/// Write both outputs or neither.
fn write_outputs(outs: &[(&Path, &[u8])]) -> Result<(), String> {
    let mut tmps: Vec<PathBuf> = vec![];
    let cleanup = |tmps: &[PathBuf]| tmps.iter().for_each(|t| drop(std::fs::remove_file(t)));
    for (p, b) in outs {
        match write_tmp(p, b) {
            Ok(t) => tmps.push(t),
            Err(e) => {
                cleanup(&tmps);
                return Err(e);
            }
        }
    }
    for (k, ((p, _), t)) in outs.iter().zip(&tmps).enumerate() {
        if let Err(e) = std::fs::rename(t, p) {
            cleanup(&tmps[k..]);
            for (q, _) in &outs[..k] {
                let _ = std::fs::remove_file(q);
            }
            return Err(format!("{}: {e}", p.display()));
        }
    }
    Ok(())
}

fn main() {
    let a = parse_args(&["public", "request", "witness", "claim-out", "proof-out"]);
    let pub_tape = std::fs::read(a["public"].join("public.bin")).unwrap_or_else(|e| die(&format!("public: {e}")));
    let req = std::fs::read(&a["request"]).unwrap_or_else(|e| die(&format!("request: {e}")));
    let wit = std::fs::read(&a["witness"]).unwrap_or_else(|e| die(&format!("witness: {e}")));
    let verbose = std::env::var("NPUDR_VERBOSE").is_ok_and(|v| v == "1");
    let work = move || -> Result<(Vec<u8>, Vec<u8>), String> {
        let t0 = std::time::Instant::now();
        let (claim, air, traces) = npudr::near::prepare(&req, &wit)?;
        if verbose {
            let shapes: Vec<String> = traces.iter().map(|m| format!("{}x{}", m.width, m.values.len() / m.width.max(1))).collect();
            eprintln!("[prove] trace {:.3}s tables {}", t0.elapsed().as_secs_f64(), shapes.join(" "));
        }
        let opts = npudr::prover::ProveOptions { verbose };
        let proof = npudr::prover::prove_bytes(&air, traces, &pub_tape, &claim, &opts)?;
        if verbose {
            eprintln!("[prove] total {:.3}s proof {} B", t0.elapsed().as_secs_f64(), proof.len());
        }
        Ok((claim, proof))
    };
    let (claim, proof) = npudr::near::with_big_stack(work).unwrap_or_else(|e| die(&e));
    write_outputs(&[(&a["claim-out"], &claim), (&a["proof-out"], &proof)]).unwrap_or_else(|e| die(&e));
}
