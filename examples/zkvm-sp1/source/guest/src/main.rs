//! SP1 guest: reads request.bin and witness.bin, runs the relation check, and
//! commits EXACTLY the canonical claim.bin bytes as the public values.
//! Any decoding error / domain violation panics => no proof can be produced.
#![no_main]
sp1_zkvm::entrypoint!(main);

pub fn main() {
    let request = sp1_zkvm::io::read_vec();
    let witness = sp1_zkvm::io::read_vec();
    match transfer_core::derive_claim(&request, &witness) {
        Ok((claim, _)) => sp1_zkvm::io::commit_slice(&claim),
        Err(e) => panic!("no claim: {}", e.reason()),
    }
}
