//! `npai-verify`: the judge-owned `verify` entry point of the `npai-v1`
//! (approved-interpreter) route.
//!
//! ```text
//! npai-verify --image <verifier.npai> --public <public.bin | public_dir>
//!             --claim <claim.bin> --proof <proof.bin> --fuel <N>
//!             [--expect-digest <sha256 hex of the image>]
//! ```
//!
//! Computes `ArenaCore.Interp.interpVerify image fuel pub claim proof`.
//! Exit codes (docs/CONTRACTS.md §4):
//!
//! * `0` — accept (`run = some true`, i.e. `HALT` on a nonzero register);
//! * `1` — not accepted: `HALT` on zero, trap, out of fuel, undecodable image,
//!   or a tape of `>= 2^32` bytes (Lean: `interpVerify = false`);
//! * `2` — usage or I/O error (no verdict);
//! * `3` — `--expect-digest` given and `sha256(image)` differs (binding
//!   failure, no verdict).
//!
//! If `--public` is a directory, the public tape is `<dir>/public.bin`.
//! stdout gets one JSON diagnostic line; it is untrusted by the worker and
//! never changes the exit code.
#![forbid(unsafe_code)]

use arena_npai::interp::{
    decode, run_full, Inputs, Outcome, MAX_CODE_LEN, MAX_MEM_SIZE, MAX_TAPE_LEN,
};
use arena_npai::report::{from_hex, to_hex};
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

/// Largest image `decode` can accept: header + max data + codeLen + max code.
const MAX_IMAGE_BYTES: u64 = 13 + MAX_MEM_SIZE + 4 + 8 * MAX_CODE_LEN;

const USAGE: &str = "usage: npai-verify --image F --public F|DIR --claim F --proof F --fuel N [--expect-digest HEX]";

fn fail(code: u8, msg: &str) -> ExitCode {
    eprintln!("npai-verify: {msg}");
    ExitCode::from(code)
}

/// `Ok(None)` = the file is at least `limit` bytes (not read).
fn read_bounded(p: &Path, limit: u64) -> std::io::Result<Option<Vec<u8>>> {
    let len = std::fs::metadata(p)?.len();
    if len >= limit {
        return Ok(None);
    }
    let b = std::fs::read(p)?;
    // Re-check: the file may have changed between stat and read.
    if b.len() as u64 >= limit {
        return Ok(None);
    }
    Ok(Some(b))
}

fn verdict(outcome: &str, digest: &str, fuel_used: Option<u64>, accept: bool) -> ExitCode {
    match fuel_used {
        Some(f) => println!("{{\"route\":\"npai-v1\",\"image_sha256\":\"{digest}\",\"outcome\":\"{outcome}\",\"fuel_used\":{f}}}"),
        None => println!("{{\"route\":\"npai-v1\",\"image_sha256\":\"{digest}\",\"outcome\":\"{outcome}\"}}"),
    }
    ExitCode::from(if accept { 0 } else { 1 })
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (mut image, mut public, mut claim, mut proof, mut fuel, mut want) =
        (None, None, None, None, None, None);
    let mut it = args.iter();
    while let Some(k) = it.next() {
        let slot = match k.as_str() {
            "--image" => &mut image,
            "--public" => &mut public,
            "--claim" => &mut claim,
            "--proof" => &mut proof,
            "--fuel" => &mut fuel,
            "--expect-digest" => &mut want,
            "-h" | "--help" => {
                println!("{USAGE}");
                return ExitCode::from(2);
            }
            _ => return fail(2, &format!("unknown argument {k:?}\n{USAGE}")),
        };
        let Some(v) = it.next() else {
            return fail(2, &format!("{k} needs a value"));
        };
        if slot.replace(v.clone()).is_some() {
            return fail(2, &format!("{k} given twice"));
        }
    }
    let (Some(image), Some(public), Some(claim), Some(proof), Some(fuel)) =
        (image, public, claim, proof, fuel)
    else {
        return fail(2, USAGE);
    };
    let Ok(fuel) = fuel.parse::<u64>() else {
        return fail(2, "--fuel must be a decimal u64");
    };
    let want = match want.map(|w| from_hex(&w.to_ascii_lowercase())) {
        None => None,
        Some(Some(d)) if d.len() == 32 => Some(d),
        Some(_) => return fail(2, "--expect-digest must be 64 hex characters"),
    };
    let mut public = PathBuf::from(public);
    if public.is_dir() {
        public.push("public.bin");
    }

    let image = match read_bounded(Path::new(&image), MAX_IMAGE_BYTES + 1) {
        Ok(b) => b,
        Err(e) => return fail(2, &format!("reading image: {e}")),
    };
    let Some(image) = image else {
        // Larger than any decodable image: decode error (and no digest to
        // bind, since we refuse to hash an unbounded file).
        if want.is_some() {
            return fail(
                3,
                "image larger than any valid NPAI image; cannot match --expect-digest",
            );
        }
        return verdict("decode_error", "", None, false);
    };
    let digest = Sha256::digest(&image);
    let digest_hex = to_hex(&digest);
    if let Some(w) = want {
        if w[..] != digest[..] {
            return fail(
                3,
                &format!(
                    "image sha256 {digest_hex} != --expect-digest {}",
                    to_hex(&w)
                ),
            );
        }
    }

    let mut tapes = Vec::with_capacity(3);
    for (name, p) in [
        ("public", public.as_path()),
        ("claim", Path::new(&claim)),
        ("proof", Path::new(&proof)),
    ] {
        match read_bounded(p, MAX_TAPE_LEN) {
            Ok(t) => tapes.push(t),
            Err(e) => return fail(2, &format!("reading {name} ({}): {e}", p.display())),
        }
    }

    // interpVerify: decode first; a decode error is rejection.
    let Some(prog) = decode(&image) else {
        return verdict("decode_error", &digest_hex, None, false);
    };
    // runWith pre-check: a tape of >= 2^32 bytes traps with fuel_used 0.
    let (Some(p), Some(c), Some(q)) = (&tapes[0], &tapes[1], &tapes[2]) else {
        return verdict("trap", &digest_hex, Some(0), false);
    };
    let (o, s) = run_full(
        &prog,
        &Inputs {
            public: p,
            claim: c,
            proof: q,
        },
        fuel,
        false,
    );
    verdict(
        o.as_str(),
        &digest_hex,
        Some(fuel - s.fuel),
        o == Outcome::Accept,
    )
}
