//! `verify --public <dir> --claim <claim.bin> --proof <proof.bin>`
//!
//! Exit 0 = accept, 1 = reject (malformed/hostile claim or proof, including
//! any panic inside the STARK verifier), 2 = error (usage, unreadable files,
//! `public.bin` malformed or prepared for a different AIR/config).
fn main() {
    let a = npstark::parse_args(&["public", "claim", "proof"]);
    let public = std::fs::read(a["public"].join("public.bin"))
        .unwrap_or_else(|e| npstark::die(&format!("public.bin: {e}")));
    let (_params, digest) = npstark::proof::parse_public(&public).unwrap_or_else(|e| npstark::die(&e));
    if digest != npstark::proof::air_config_digest() {
        npstark::die("public.bin was prepared for a different AIR/config");
    }
    let claim = std::fs::read(&a["claim"]).unwrap_or_else(|e| npstark::die(&format!("claim: {e}")));
    let meta = std::fs::metadata(&a["proof"]).unwrap_or_else(|e| npstark::die(&format!("proof: {e}")));
    if meta.len() > npstark::proof::MAX_PROOF_BYTES as u64 {
        eprintln!("reject: proof too large");
        std::process::exit(1);
    }
    let proof = std::fs::read(&a["proof"]).unwrap_or_else(|e| npstark::die(&format!("proof: {e}")));
    std::panic::set_hook(Box::new(|_| {}));
    let r = std::panic::catch_unwind(|| npstark::proof::verify(&claim, &proof));
    match r {
        Ok(Ok(())) => std::process::exit(0),
        Ok(Err(e)) => {
            eprintln!("reject: {e}");
            std::process::exit(1)
        }
        Err(_) => {
            eprintln!("reject: verifier panicked on hostile input");
            std::process::exit(1)
        }
    }
}
