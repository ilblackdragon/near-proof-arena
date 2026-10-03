//! prepare --params <approved_params.bin> --out <public_dir>
//!
//! Run by the JUDGE. Derives the SP1 program verifying key from the guest ELF
//! compiled into this binary (deterministic: SP1 `setup` is a pure function of
//! the ELF) and writes public_dir/public.bin. No key material is chosen by the
//! candidate: the vkey is a hash of the program's preprocessed traces.
use sp1_sdk::blocking::{Prover, ProverClient};
use sp1_sdk::{HashableKey, ProvingKey, SP1_CIRCUIT_VERSION};
use zk_artifacts::{arg, hex, sha256, Public, GUEST_ELF_SHA256, PUBLIC_FILE};
use zk_prover::{die, GUEST_ELF};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (Some(params), Some(out)) = (arg(&args, "--params"), arg(&args, "--out")) else {
        die(2, "usage: prepare --params <params.bin> --out <public_dir>")
    };
    let params = std::fs::read(&params).unwrap_or_else(|e| die(2, format!("read params: {e}")));
    if params != transfer_core::expected_params() {
        die(2, "params.bin is not the approved params of near/pv86/receipt-transfer-batch/v0");
    }
    if sha256(&GUEST_ELF) != GUEST_ELF_SHA256 {
        die(2, "embedded guest ELF does not match its pinned digest");
    }
    let client = ProverClient::builder().light().build();
    let pk = client.setup(GUEST_ELF).unwrap_or_else(|e| die(2, format!("setup: {e}")));
    let vk = pk.verifying_key();
    let public = Public {
        params_sha256: sha256(&params),
        elf_sha256: GUEST_ELF_SHA256,
        vk_hash: vk.hash_u32(),
        circuit_version: SP1_CIRCUIT_VERSION.trim().as_bytes().to_vec(),
    };
    std::fs::create_dir_all(&out).unwrap_or_else(|e| die(2, format!("mkdir: {e}")));
    let path = std::path::Path::new(&out).join(PUBLIC_FILE);
    std::fs::write(&path, public.encode()).unwrap_or_else(|e| die(2, format!("write: {e}")));
    eprintln!("prepare: guest elf sha256 {} vkey {}", hex(&GUEST_ELF_SHA256), vk.bytes32());
}
