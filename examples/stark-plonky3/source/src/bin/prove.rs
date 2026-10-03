//! `prove --public <dir> --request <request.bin> --witness <witness.bin>
//!        --claim-out <claim.bin> --proof-out <proof.bin>`
//!
//! Exit 0 on success; 3 if the request is out of the challenge domain (or the
//! witness does not reveal it); 2 on any other error.
fn main() {
    let a = npstark::parse_args(&["public", "request", "witness", "claim-out", "proof-out"]);
    let public = std::fs::read(a["public"].join("public.bin"))
        .unwrap_or_else(|e| npstark::die(&format!("public.bin: {e}")));
    let (_p, d) = npstark::proof::parse_public(&public).unwrap_or_else(|e| npstark::die(&e));
    if d != npstark::proof::air_config_digest() {
        npstark::die("public.bin was prepared for a different AIR/config");
    }
    let req = std::fs::read(&a["request"]).unwrap_or_else(|e| npstark::die(&format!("request: {e}")));
    let wit = std::fs::read(&a["witness"]).unwrap_or_else(|e| npstark::die(&format!("witness: {e}")));
    let (claim, proof, _st) = match npstark::proof::prove(&req, &wit, false) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("refused: {e}");
            std::process::exit(if e.contains("out of domain") || e.contains("not in trie") { 3 } else { 2 });
        }
    };
    std::fs::write(&a["claim-out"], claim).unwrap_or_else(|e| npstark::die(&format!("claim-out: {e}")));
    std::fs::write(&a["proof-out"], proof).unwrap_or_else(|e| npstark::die(&format!("proof-out: {e}")));
}
