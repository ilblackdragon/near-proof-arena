//! `prove --public <dir> --request <request.bin> --witness <witness.bin>
//!        --claim-out <claim.bin> --proof-out <proof.bin>`
fn main() {
    let a = reexec::parse_args(&["public", "request", "witness", "claim-out", "proof-out"]);
    let req = std::fs::read(&a["request"]).unwrap_or_else(|e| reexec::die(&format!("request: {e}")));
    let wit = std::fs::read(&a["witness"]).unwrap_or_else(|e| reexec::die(&format!("witness: {e}")));
    let (claim, proof) = reexec::engine::prove(&req, &wit).unwrap_or_else(|e| reexec::die(&e));
    std::fs::write(&a["claim-out"], claim).unwrap_or_else(|e| reexec::die(&format!("claim-out: {e}")));
    std::fs::write(&a["proof-out"], proof).unwrap_or_else(|e| reexec::die(&format!("proof-out: {e}")));
}
