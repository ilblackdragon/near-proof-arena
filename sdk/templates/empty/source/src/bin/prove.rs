//! `prove --public <dir> --request <request.bin> --witness <witness.bin>
//!        --claim-out <claim.bin> --proof-out <proof.bin>`
//!
//! The only entry point that receives the witness. Must write the canonical
//! claim (spec/claim-v1.md) for `request` — the judge compares it byte-for-byte
//! with the oracle's expected claim (CLAIM_MISMATCH otherwise) — and a proof.
//! No network, no state other than `public_dir` survives between calls.
fn main() {
    let _a = candidate::parse_args(&["public", "request", "witness", "claim-out", "proof-out"]);
    // TODO: implement. Exiting non-zero is reported as PROVER_FAILED.
    candidate::die("prove is not implemented in the empty template");
}
