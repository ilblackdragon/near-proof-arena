//! Byte formats of the candidate's own artifacts.
//!
//! `public_dir/public.bin` (written by the judge-run `prepare`):
//! ```text
//! bytes  "nearproof-sp1-public-v1"
//! bytes  statement_id                    = near/pv86/receipt-transfer-batch/v0
//! hash   sha256(params.bin)              (must be the challenge's params)
//! hash   sha256(guest ELF)               (must equal the digest compiled into verify)
//! u32x8  SP1 program vkey hash           (KoalaBear canonical u32, little endian)
//! bytes  SP1 circuit version             (e.g. "v6.0.0")
//! ```
//! `proof.bin` (written by `prove`): `bytes "nearproof-sp1-compressed-v1" ‖ bincode(SP1RecursionProof)`.
//! The public values are NOT in proof.bin: `verify` uses claim.bin itself as the
//! public values, so the proof can only be accepted for those exact bytes.
use sha2::{Digest, Sha256};

include!(concat!(env!("OUT_DIR"), "/elf_digest.rs"));

pub const PUBLIC_FORMAT: &[u8] = b"nearproof-sp1-public-v1";
pub const PROOF_FORMAT: &[u8] = b"nearproof-sp1-compressed-v1";
pub const PUBLIC_FILE: &str = "public.bin";
/// Upper bound on proof.bin accepted by verify (honest proofs are ~1.3 MB).
pub const MAX_PROOF_BYTES: usize = 8 << 20;

pub fn sha256(b: &[u8]) -> [u8; 32] {
    Sha256::digest(b).into()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Public {
    pub params_sha256: [u8; 32],
    pub elf_sha256: [u8; 32],
    pub vk_hash: [u32; 8],
    pub circuit_version: Vec<u8>,
}

fn put_bytes(out: &mut Vec<u8>, b: &[u8]) {
    out.extend_from_slice(&(b.len() as u32).to_le_bytes());
    out.extend_from_slice(b);
}

impl Public {
    pub fn encode(&self) -> Vec<u8> {
        let mut o = Vec::new();
        put_bytes(&mut o, PUBLIC_FORMAT);
        put_bytes(&mut o, transfer_core::STATEMENT_ID);
        o.extend_from_slice(&self.params_sha256);
        o.extend_from_slice(&self.elf_sha256);
        for w in self.vk_hash {
            o.extend_from_slice(&w.to_le_bytes());
        }
        put_bytes(&mut o, &self.circuit_version);
        o
    }

    /// Strict decode + the checks every consumer must make: right statement,
    /// right params, and the guest ELF this binary was built with.
    pub fn decode_checked(b: &[u8]) -> Result<Self, &'static str> {
        struct Cur<'a>(&'a [u8], usize);
        impl<'a> Cur<'a> {
            fn take(&mut self, n: usize) -> Result<&'a [u8], &'static str> {
                let end = self.1.checked_add(n).ok_or("overflow")?;
                let s = self.0.get(self.1..end).ok_or("public.bin truncated")?;
                self.1 = end;
                Ok(s)
            }
            fn bytes(&mut self) -> Result<&'a [u8], &'static str> {
                let n = u32::from_le_bytes(self.take(4)?.try_into().unwrap()) as usize;
                if n > 64 {
                    return Err("public.bin field too long");
                }
                self.take(n)
            }
        }
        let mut c = Cur(b, 0);
        if c.bytes()? != PUBLIC_FORMAT {
            return Err("public.bin format tag");
        }
        if c.bytes()? != transfer_core::STATEMENT_ID {
            return Err("public.bin statement id");
        }
        let params_sha256: [u8; 32] = c.take(32)?.try_into().unwrap();
        let elf_sha256: [u8; 32] = c.take(32)?.try_into().unwrap();
        let mut vk_hash = [0u32; 8];
        for w in vk_hash.iter_mut() {
            *w = u32::from_le_bytes(c.take(4)?.try_into().unwrap());
        }
        let circuit_version = c.bytes()?.to_vec();
        if c.1 != b.len() {
            return Err("public.bin trailing bytes");
        }
        if params_sha256 != sha256(&transfer_core::expected_params()) {
            return Err("public.bin params digest is not this challenge's params");
        }
        if elf_sha256 != GUEST_ELF_SHA256 {
            return Err("public.bin guest ELF digest != the ELF this binary was built with");
        }
        Ok(Public { params_sha256, elf_sha256, vk_hash, circuit_version })
    }
}

/// Minimal `--flag value` argument parsing shared by the entry points.
pub fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

pub fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
