//! verify --public <public_dir> --claim <claim.bin> --proof <proof.bin>
//!
//! Exit 0 = accept, 1 = reject, 2 = usage / public_dir error (never accept).
//!
//! Accepts iff ALL of:
//! * public_dir/public.bin is well formed, for this statement and the
//!   challenge's params, and names the guest ELF digest compiled into this
//!   binary (so the vkey came from a `prepare` built from the same guest);
//! * claim.bin is a structurally well-formed near-arena-claim-v1 claim;
//! * proof.bin is a framed SP1 compressed (recursion) proof that the SP1 v6.8.1
//!   compressed verifier accepts: the shard proof verifies, the recursion vk is
//!   in the pinned recursion-vk Merkle tree, the proof is complete, its program
//!   vkey digest equals public.bin's vkey, and its committed public-values
//!   digest equals SHA-256 (or BLAKE3) of claim.bin;
//! * the guest exit code is 0.
//! All decoding of hostile bytes is bounded and panics are caught (=> reject).
use slop_algebra::{AbstractField, PrimeField32};
use sp1_hypercube::{SP1PcsProofInner, SP1RecursionProof};
use sp1_primitives::{SP1Field, SP1GlobalContext};
use sp1_recursion_executor::RecursionPublicValues;
use sp1_verifier::compressed::SP1CompressedVerifier;
use std::borrow::Borrow;
use zk_artifacts::{arg, Public, MAX_PROOF_BYTES, PROOF_FORMAT, PUBLIC_FILE};

type Proof = SP1RecursionProof<SP1GlobalContext, SP1PcsProofInner>;

fn reject(msg: &str) -> ! {
    eprintln!("verify: REJECT: {msg}");
    std::process::exit(1)
}

fn read_capped(path: &str, cap: usize) -> Result<Vec<u8>, String> {
    use std::io::Read;
    let f = std::fs::File::open(path).map_err(|e| format!("open {path}: {e}"))?;
    let mut v = Vec::new();
    f.take(cap as u64 + 1).read_to_end(&mut v).map_err(|e| format!("read {path}: {e}"))?;
    if v.len() > cap {
        return Err(format!("{path} exceeds {cap} bytes"));
    }
    Ok(v)
}

fn check(public: &Public, claim: &[u8], proof_bytes: &[u8]) -> Result<(), String> {
    if !transfer_core::claim_well_formed(claim) {
        return Err("claim.bin is not a well-formed near-arena-claim-v1 claim".into());
    }
    let tag_len = PROOF_FORMAT.len();
    if proof_bytes.len() < 4 + tag_len
        || proof_bytes[..4] != (tag_len as u32).to_le_bytes()
        || &proof_bytes[4..4 + tag_len] != PROOF_FORMAT
    {
        return Err("proof.bin format tag".into());
    }
    use bincode::Options;
    let proof: Proof = bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(MAX_PROOF_BYTES as u64)
        .reject_trailing_bytes()
        .deserialize(&proof_bytes[4 + tag_len..])
        .map_err(|e| format!("proof.bin decode: {e}"))?;
    let vk_hash: [SP1Field; 8] = public.vk_hash.map(SP1Field::from_canonical_u32);
    let verifier = SP1CompressedVerifier::new();
    verifier
        .verify_compressed_with_public_values(&proof, claim, &vk_hash)
        .map_err(|e| format!("SP1 compressed verification: {e}"))?;
    let pv: &RecursionPublicValues<SP1Field> = proof.proof.public_values.as_slice().borrow();
    if pv.exit_code != SP1Field::zero() {
        return Err(format!("guest exit code {}", pv.exit_code.as_canonical_u32()));
    }
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (Some(public_dir), Some(claim), Some(proof)) =
        (arg(&args, "--public"), arg(&args, "--claim"), arg(&args, "--proof"))
    else {
        eprintln!("usage: verify --public <dir> --claim <claim.bin> --proof <proof.bin>");
        std::process::exit(2)
    };
    let public_path = std::path::Path::new(&public_dir).join(PUBLIC_FILE);
    let public = match read_capped(&public_path.to_string_lossy(), 4096)
        .and_then(|b| Public::decode_checked(&b).map_err(String::from))
    {
        Ok(p) => p,
        Err(e) => {
            eprintln!("verify: public_dir error: {e}");
            std::process::exit(2)
        }
    };
    let claim = read_capped(&claim, transfer_core::MAX_CLAIM_BYTES).unwrap_or_else(|e| reject(&e));
    let proof = read_capped(&proof, MAX_PROOF_BYTES).unwrap_or_else(|e| reject(&e));
    // Hostile proofs may trip assertions inside the verifier: a panic is a reject.
    std::panic::set_hook(Box::new(|_| {}));
    match std::panic::catch_unwind(|| check(&public, &claim, &proof)) {
        Ok(Ok(())) => {
            eprintln!("verify: ACCEPT");
            std::process::exit(0)
        }
        Ok(Err(e)) => reject(&e),
        Err(_) => reject("verifier panicked on malformed proof"),
    }
}
