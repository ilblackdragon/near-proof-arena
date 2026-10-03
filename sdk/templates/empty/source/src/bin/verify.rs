//! `verify --public <dir> --claim <claim.bin> --proof <proof.bin>`
//!
//! Exit 0 = accept, 1 = reject, anything else = error (never accept).
//! Receives NO witness, request or expected result. Must be deterministic and
//! must reject hostile proof bytes (the judge fuzzes it). This is the
//! artifact your formal certificate is about: changing it reopens every formal
//! obligation.
fn main() {
    let a = candidate::parse_args(&["public", "claim", "proof"]);
    for k in ["claim", "proof"] {
        if let Err(e) = std::fs::read(&a[k]) {
            candidate::die(&format!("{k}: {e}"));
        }
    }
    // TODO: implement. The template rejects everything — the only safe default.
    std::process::exit(1);
}
