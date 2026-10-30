//! Versioned generator code registry. Signed v3-d3 sources and default contracts remain unchanged.
#[path = "../../v3-d3/src/d3contracts.rs"]
mod baseline;
pub use baseline::{RICH, TINY, TTN2, HOSTX, code_facts};
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
    // opt-in cross-family scenario contracts (src/xfam.rs)
    contracts.extend(crate::xfam::contracts());
    if let Some(code) = code {
        let entry = contracts.iter_mut().find(|(name, _)| *name == "d3float").unwrap();
        entry.1 = code.clone();
    }
    if crate::d3gen::scenario() == Some(crate::d3gen::Scenario::CurveHosts) {
        contracts.push((crate::curve_hosts::CODE_NAME, crate::curve_hosts::code().to_vec()));
    }
    if crate::d3gen::scenario() == Some(crate::d3gen::Scenario::PipelineRace) {
        const NAMES: [&str; crate::d3gen::RACE_ROUNDS] = ["race00", "race01", "race02", "race03",
            "race04", "race05", "race06", "race07", "race08", "race09", "race10", "race11",
            "race12", "race13", "race14", "race15"];
        for (k, code) in crate::d3gen::race_codes().iter().enumerate() {
            contracts.push((NAMES[k], code.clone()));
        }
    }
    if crate::keys::enabled() {
        contracts.push(("kgashost", crate::keys::host_code()));
    }
    if crate::keys::mldsa_mode() {
        contracts.push(("kmlpk", crate::keys::mlpk_code()));
    }
    contracts
}

/// Baseline call marks, plus `e.ood_host` for every method of the curve-hosts scenario contract
/// (each one calls a curve host unconditionally).
pub fn ood_call(name: &str, method: &str) -> Option<&'static str> {
    if name == crate::curve_hosts::CODE_NAME || name == "xcurve" {
        return Some("e.ood_host");
    }
    baseline::ood_call(name, method)
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
