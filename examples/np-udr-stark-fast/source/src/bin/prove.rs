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

/// Runtime CPU dispatch: the package ships `prove` (x86-64-v3, AVX2) and
/// `prove-avx512` (x86-64-v4, same source). On a CPU with AVX-512 F/BW/DQ/VL
/// this binary replaces itself (execve, same arguments and environment) with
/// the sibling `prove-avx512`; both compute the same proof bytes.
/// `NPUDR_NO_AVX512=1` disables the switch.
fn dispatch_avx512() {
    #[cfg(all(target_arch = "x86_64", not(target_feature = "avx512f")))]
    {
        use std::os::unix::process::CommandExt;
        if std::env::var_os("NPUDR_NO_AVX512").is_some() {
            return;
        }
        let ok = std::arch::is_x86_feature_detected!("avx512f")
            && std::arch::is_x86_feature_detected!("avx512bw")
            && std::arch::is_x86_feature_detected!("avx512dq")
            && std::arch::is_x86_feature_detected!("avx512vl");
        if !ok {
            return;
        }
        let Some(sib) = std::env::current_exe().ok().and_then(|p| Some(p.parent()?.join("prove-avx512"))) else { return };
        if !sib.is_file() {
            return;
        }
        let err = std::process::Command::new(&sib).args(std::env::args_os().skip(1)).exec();
        // exec failed: fall through to the AVX2 code path
        eprintln!("[prove] avx512 dispatch failed ({err}); using the AVX2 build");
    }
}

fn main() {
    dispatch_avx512();
    let a = parse_args(&["public", "request", "witness", "claim-out", "proof-out"]);
    let pub_tape = std::fs::read(a["public"].join("public.bin")).unwrap_or_else(|e| die(&format!("public: {e}")));
    let req = std::fs::read(&a["request"]).unwrap_or_else(|e| die(&format!("request: {e}")));
    let wit = std::fs::read(&a["witness"]).unwrap_or_else(|e| die(&format!("witness: {e}")));
    let verbose = std::env::var("NPUDR_VERBOSE").is_ok_and(|v| v == "1");
    let work = move || -> Result<(Vec<u8>, Vec<u8>), String> {
        let t0 = std::time::Instant::now();
        let (claim, air, traces) = npudr::near::prepare_cols(&req, &wit)?;
        if verbose {
            let shapes: Vec<String> = traces.iter().map(|m| format!("{}x2^{}", m.width(), m.log_h)).collect();
            let bytes: usize = traces.iter().map(|m| m.bytes()).sum();
            eprintln!("[prove] trace {:.3}s tables {} ({} MB)", t0.elapsed().as_secs_f64(), shapes.join(" "), bytes >> 20);
        }
        let opts = npudr::prover::ProveOptions { verbose };
        let proof = npudr::prover::prove_cols_bytes(&air, traces, &pub_tape, &claim, &opts)?;
        if verbose {
            eprintln!("[prove] total {:.3}s proof {} B", t0.elapsed().as_secs_f64(), proof.len());
        }
        Ok((claim, proof))
    };
    let (claim, proof) = npudr::near::with_big_stack(work).unwrap_or_else(|e| die(&e));
    write_outputs(&[(&a["claim-out"], &claim), (&a["proof-out"], &proof)]).unwrap_or_else(|e| die(&e));
}
