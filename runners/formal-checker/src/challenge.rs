//! Per-challenge formal configuration: which judge-trusted Lean packages a
//! challenge's statement depends on, and how its Expected module is rendered.
//!
//! Config files live in `runners/formal-checker/challenges/<name>.json`
//! (`arena-formal-challenge-v1`). Paths are relative to the repository root
//! and must point at a *clean* checkout (no `.lake/`), because trusted
//! package tree digests are bound into the reference-build cache key.

use crate::expected::{LeanValue, TemplateExpected};
use crate::pipeline::TrustedPackage;
use arena_types::SecurityProfile;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::Path;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustedPackageConfig {
    pub name: String,
    /// Directory relative to the repository root.
    pub src_root: String,
    pub include: Option<Vec<String>>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExpectedConfig {
    pub module: String,
    pub decl: String,
    /// Template path relative to the repository root.
    pub template: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ChallengeFormalConfig {
    pub schema: String,
    pub challenge: String,
    pub trusted: Vec<TrustedPackageConfig>,
    /// Module prefixes candidates may not define (judge namespaces).
    pub reserved_prefixes: Vec<String>,
    pub expected: ExpectedConfig,
}

/// Values the Expected template needs, taken from the frozen challenge
/// definition (`security_profile`, `formal_params`) and the judge's build.
#[derive(Clone, Debug)]
pub struct ExpectedInputs<'a> {
    pub profile: &'a SecurityProfile,
    pub verify_fuel: u64,
    pub max_proof_bytes: u64,
    pub max_reduction_fuel: u64,
    /// sha256(public.bin), lowercase hex.
    pub public_digest_hex: String,
    /// sha256(verifier.npai), lowercase hex.
    pub verifier_digest_hex: String,
}

#[derive(Debug, thiserror::Error)]
pub enum ConfigError {
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
    #[error("json: {0}")]
    Json(#[from] serde_json::Error),
    #[error("invalid config: {0}")]
    Invalid(String),
}

impl ChallengeFormalConfig {
    pub fn load(path: &Path) -> Result<Self, ConfigError> {
        let c: Self = serde_json::from_slice(&std::fs::read(path)?)?;
        if c.schema != "arena-formal-challenge-v1" {
            return Err(ConfigError::Invalid(format!("unknown schema {}", c.schema)));
        }
        for t in &c.trusted {
            if t.src_root.starts_with('/') || t.src_root.split('/').any(|s| s == "..") {
                return Err(ConfigError::Invalid(format!("src_root must be repo-relative: {}", t.src_root)));
            }
        }
        Ok(c)
    }

    pub fn trusted_packages(&self, repo_root: &Path) -> Vec<TrustedPackage> {
        self.trusted
            .iter()
            .map(|t| TrustedPackage { name: t.name.clone(), src_root: repo_root.join(&t.src_root), include: t.include.clone() })
            .collect()
    }

    /// Render the challenge's Expected template with literal data.
    pub fn expected(&self, repo_root: &Path, inp: &ExpectedInputs) -> Result<TemplateExpected, ConfigError> {
        let template = std::fs::read_to_string(repo_root.join(&self.expected.template))?;
        let p = inp.profile;
        let model = serde_json::to_value(p.model)?.as_str().unwrap_or_default().to_string();
        let mut data: BTreeMap<String, LeanValue> = BTreeMap::new();
        data.insert("profile_id".into(), LeanValue::Str(p.id.clone()));
        data.insert("profile_model".into(), LeanValue::Str(model));
        data.insert("target_bits".into(), LeanValue::Nat(p.target_bits.to_string()));
        data.insert("max_prover_queries_log2".into(), LeanValue::Nat(p.max_prover_queries_log2.to_string()));
        data.insert("max_hash_queries_log2".into(), LeanValue::Nat(p.max_hash_queries_log2.to_string()));
        let n_slots = (0..).take_while(|i| template.contains(&format!("{{{{assumption_{i}}}}}"))).count();
        if p.allowed_assumptions.len() != n_slots {
            return Err(ConfigError::Invalid(format!(
                "template has {n_slots} assumption slots, profile lists {}",
                p.allowed_assumptions.len()
            )));
        }
        for (i, a) in p.allowed_assumptions.iter().enumerate() {
            data.insert(format!("assumption_{i}"), LeanValue::Str(a.clone()));
        }
        data.insert("verify_fuel".into(), LeanValue::Nat(inp.verify_fuel.to_string()));
        data.insert("max_proof_bytes".into(), LeanValue::Nat(inp.max_proof_bytes.to_string()));
        data.insert("max_reduction_fuel".into(), LeanValue::Nat(inp.max_reduction_fuel.to_string()));
        data.insert("public_digest".into(), LeanValue::Bytes(inp.public_digest_hex.clone()));
        data.insert("verifier_digest".into(), LeanValue::Bytes(inp.verifier_digest_hex.clone()));
        Ok(TemplateExpected { module: self.expected.module.clone(), decl: self.expected.decl.clone(), template, data })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expected::ExpectedTypeBuilder;

    fn repo_root() -> std::path::PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    #[test]
    fn near_transfer_config_renders() {
        let root = repo_root();
        let cfg = ChallengeFormalConfig::load(&root.join("runners/formal-checker/challenges/near-transfer-receipt-v1.json")).unwrap();
        for t in cfg.trusted_packages(&root) {
            assert!(t.src_root.is_dir(), "{}", t.src_root.display());
        }
        let profile: SecurityProfile =
            serde_json::from_slice(&std::fs::read(root.join("security/profiles/validity-classical-128.json")).unwrap()).unwrap();
        let inp = ExpectedInputs {
            profile: &profile,
            verify_fuel: 1 << 30,
            max_proof_bytes: 8 << 20,
            max_reduction_fuel: 1 << 30,
            public_digest_hex: "00".repeat(32),
            verifier_digest_hex: "11".repeat(32),
        };
        let src = cfg.expected(&root, &inp).unwrap().render().unwrap();
        assert!(src.contains("import NearSpec.Challenge"));
        assert!(src.contains("(1073741824 : Nat) (8388608 : Nat) (1073741824 : Nat)"));
        assert!(src.contains("[\"sha256-collision-resistance\", \"random-oracle-fiat-shamir-sha256\"]"));
        assert!(!src.contains("{{"));
    }
}
