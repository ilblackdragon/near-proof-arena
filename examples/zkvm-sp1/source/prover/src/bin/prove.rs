//! prove --public <dir> --request <request.bin> --witness <witness.bin>
//!       --claim-out <claim.bin> --proof-out <proof.bin>
//!
//! 1. native pre-check (same `transfer-core` code as the guest): refuse
//!    out-of-domain / malformed inputs fast (exit 3);
//! 2. SP1 CPU prover: execute the guest on (request, witness), prove the
//!    execution, recursively compress to one constant-size STARK proof;
//! 3. write claim.bin = the guest's public values (the canonical claim) and
//!    proof.bin = framed compressed proof. The witness is not in the proof.
use sp1_sdk::blocking::{ProveRequest, Prover, ProverClient};
use sp1_sdk::{HashableKey, ProvingKey, SP1Proof, SP1Stdin};
use std::time::Instant;
use zk_artifacts::{arg, Public, PROOF_FORMAT, PUBLIC_FILE};
use zk_prover::{die, GUEST_ELF};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let need = |n: &str| arg(&args, n).unwrap_or_else(|| die(2, format!("missing {n}")));
    let (public_dir, request, witness) = (need("--public"), need("--request"), need("--witness"));
    let (claim_out, proof_out) = (need("--claim-out"), need("--proof-out"));

    let public_bytes = std::fs::read(std::path::Path::new(&public_dir).join(PUBLIC_FILE))
        .unwrap_or_else(|e| die(2, format!("read public.bin: {e}")));
    let public = Public::decode_checked(&public_bytes).unwrap_or_else(|e| die(2, e));
    let request = std::fs::read(&request).unwrap_or_else(|e| die(2, format!("read request: {e}")));
    let witness = std::fs::read(&witness).unwrap_or_else(|e| die(2, format!("read witness: {e}")));

    let t = Instant::now();
    let (claim, stats) = transfer_core::derive_claim(&request, &witness)
        .unwrap_or_else(|e| die(3, format!("refusing to prove: {e:?}")));
    eprintln!("prove: native check ok in {:?}: {stats:?}", t.elapsed());

    let t = Instant::now();
    let client = ProverClient::builder().cpu().build();
    let pk = client.setup(GUEST_ELF).unwrap_or_else(|e| die(2, format!("setup: {e}")));
    if pk.verifying_key().hash_u32() != public.vk_hash {
        die(2, "program vkey differs from public.bin (different guest build?)");
    }
    eprintln!("prove: client+setup {:?}", t.elapsed());

    let mut stdin = SP1Stdin::new();
    stdin.write_vec(request);
    stdin.write_vec(witness);
    let t = Instant::now();
    let proof = client.prove(&pk, stdin).compressed().run().unwrap_or_else(|e| die(2, format!("prove: {e}")));
    eprintln!("prove: compressed proof in {:?}", t.elapsed());

    if proof.public_values.as_slice() != claim.as_slice() {
        die(2, "guest public values differ from the native claim (bug)");
    }
    let SP1Proof::Compressed(inner) = proof.proof else { die(2, "expected a compressed proof") };
    let mut out = Vec::new();
    out.extend_from_slice(&(PROOF_FORMAT.len() as u32).to_le_bytes());
    out.extend_from_slice(PROOF_FORMAT);
    bincode::serialize_into(&mut out, &inner).unwrap_or_else(|e| die(2, format!("serialize: {e}")));
    std::fs::write(&claim_out, &claim).unwrap_or_else(|e| die(2, format!("write claim: {e}")));
    std::fs::write(&proof_out, &out).unwrap_or_else(|e| die(2, format!("write proof: {e}")));
    eprintln!("prove: claim {} bytes, proof {} bytes", claim.len(), out.len());
}
