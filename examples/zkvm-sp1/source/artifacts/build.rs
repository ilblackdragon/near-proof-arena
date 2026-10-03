//! Pins the guest ELF: its SHA-256 becomes a compile-time constant of every
//! host binary (prepare/prove embed the bytes, verify only the digest).
use sha2::{Digest, Sha256};
fn main() {
    let elf = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../guest-elf/transfer-guest.elf");
    println!("cargo:rerun-if-changed={}", elf.display());
    let bytes = std::fs::read(&elf).expect("guest-elf/transfer-guest.elf missing: run build-recipe/build.sh");
    let d: [u8; 32] = Sha256::digest(&bytes).into();
    let out = std::path::Path::new(&std::env::var("OUT_DIR").unwrap()).join("elf_digest.rs");
    std::fs::write(out, format!("pub const GUEST_ELF_SHA256: [u8; 32] = {d:?};\n")).unwrap();
}
