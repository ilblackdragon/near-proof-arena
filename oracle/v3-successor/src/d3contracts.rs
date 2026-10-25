//! Versioned generator code registry. Signed v3-d3 sources and default contracts remain unchanged.
#[path = "../../v3-d3/src/d3contracts.rs"]
mod baseline;
pub use baseline::{RICH, TINY, TTN2, HOSTX, code_facts, ood_call};
use near_primitives::hash::CryptoHash;
use std::collections::BTreeMap;
use std::sync::OnceLock;

/// Replace only the test account d3float; the exact bytes are included in witness code blobs.
/// A configured unreadable/empty file is a hard error, never a fallback to old fixtures.
pub fn all() -> Vec<(&'static str, Vec<u8>)> {
    static CODE: OnceLock<Option<Vec<u8>>> = OnceLock::new();
    let code = CODE.get_or_init(|| {
        std::env::var_os("NEAR_SUCCESSOR_CONTRACT").map(|path| {
            let bytes = std::fs::read(path).expect("read NEAR_SUCCESSOR_CONTRACT");
            assert!(!bytes.is_empty(), "NEAR_SUCCESSOR_CONTRACT must not be empty");
            bytes
        })
    });
    let mut contracts = baseline::all();
    // opt-in yield / storage-limits scenario contracts (none for the baseline and global-cache)
    contracts.extend(crate::scenarios::contracts());
    if let Some(code) = code {
        let entry = contracts.iter_mut().find(|(name, _)| *name == "d3float").unwrap();
        entry.1 = code.clone();
    }
    contracts
}

pub struct Registry {
    pub by_hash: BTreeMap<CryptoHash, (&'static str, Vec<u8>)>,
}

pub fn registry() -> &'static Registry {
    static REGISTRY: OnceLock<Registry> = OnceLock::new();
    REGISTRY.get_or_init(|| Registry {
        by_hash: all().into_iter().map(|(n, c)| (CryptoHash::hash_bytes(&c), (n,c))).collect(),
    })
}
