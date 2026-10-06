//! `prove --public <dir> --request <request.bin> --witness <witness.bin>
//!        --claim-out <claim.bin> --proof-out <proof.bin>`
//!
//! `near/pv86/chunk-validation/v0` has no request file: the request IS the
//! claim (`near-arena-claim-v3`), so `claim.bin` = `request.bin`. The proof is
//! the witness itself (`near-arena-witness-v3`: the real nearcore
//! `ChunkStateWitness` borsh + contract code), verbatim; the verifier decides
//! `RelD0 claim proof` (`formal/ReexecV3D0/Model.lean`).
//!
//! The prover only checks the two format tags. It does not decide the
//! relation: on a false or out-of-domain claim it still emits a proof, which
//! the verifier rejects.

fn die(msg: &str) -> ! {
    eprintln!("error: {msg}");
    std::process::exit(2)
}

fn tagged(b: &[u8], tag: &[u8]) -> bool {
    b.len() >= 4 + tag.len()
        && u32::from_le_bytes([b[0], b[1], b[2], b[3]]) as usize == tag.len()
        && &b[4..4 + tag.len()] == tag
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let get = |name: &str| -> String {
        let i = args
            .iter()
            .position(|a| a == &format!("--{name}"))
            .unwrap_or_else(|| die(&format!("missing --{name}")));
        args.get(i + 1).cloned().unwrap_or_else(|| die(&format!("--{name} needs a value")))
    };
    let (_public, request, witness, claim_out, proof_out) =
        (get("public"), get("request"), get("witness"), get("claim-out"), get("proof-out"));
    if args.len() != 10 {
        die("usage: prove --public DIR --request FILE --witness FILE --claim-out FILE --proof-out FILE");
    }
    let claim = std::fs::read(&request).unwrap_or_else(|e| die(&format!("request: {e}")));
    let wit = std::fs::read(&witness).unwrap_or_else(|e| die(&format!("witness: {e}")));
    if !tagged(&claim, b"near-arena-claim-v3") {
        die("request: not a near-arena-claim-v3 claim");
    }
    if !tagged(&wit, b"near-arena-witness-v3") {
        die("witness: not a near-arena-witness-v3 witness");
    }
    std::fs::write(&claim_out, &claim).unwrap_or_else(|e| die(&format!("claim-out: {e}")));
    std::fs::write(&proof_out, &wit).unwrap_or_else(|e| die(&format!("proof-out: {e}")));
}
