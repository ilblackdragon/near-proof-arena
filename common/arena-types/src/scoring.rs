//! Scoring kinds and the governed price model (contracts v1.5, additive;
//! docs/BENCHMARK_SPEC.md §14 "cost board").
//!
//! A challenge without a `scoring` section is scored by speed only
//! (bench-spec-v1 §8), exactly as before; its id is unchanged because the
//! field is not serialized when absent. A challenge with
//! `scoring.kind = cost_v1` pins a [`PriceModel`] (inline, plus its JCS
//! digest) and the per-class cost components of its reference candidate; it
//! gets **two** boards — the speed board (unchanged) and the cost board —
//! and scores of different kinds are never compared or merged.

use crate::{canonical, Digest};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

pub const PRICE_MODEL_SCHEMA: &str = "arena-price-model-v1";
/// The only unit in `arena-price-model-v1`: femto-USD (1e-15 USD), integers.
pub const PRICE_MODEL_UNIT: &str = "femto_usd";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum ScoringKind {
    /// bench-spec-v1 §8: weighted geometric mean of prove-time speedups.
    Speed,
    /// bench-spec §14: weighted geometric mean of per-class system-cost
    /// ratios under a pinned [`PriceModel`].
    CostV1,
}

impl ScoringKind {
    pub fn as_str(self) -> &'static str {
        match self {
            ScoringKind::Speed => "speed",
            ScoringKind::CostV1 => "cost_v1",
        }
    }
}

/// Why a price-model parameter has its value (part of the hashed object, so
/// the rationale cannot be edited without a new version).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct PriceRationale {
    /// Field name of the parameter, e.g. `validators_per_chunk`.
    pub param: String,
    /// `protocol` (read from pinned nearcore), `published` (public price
    /// list / docs), or `estimate` (a modelling choice).
    pub basis: String,
    pub note: String,
    pub sources: Vec<String>,
}

/// `arena-price-model-v1`: integers only, femto-USD. Per-chunk system cost
/// of one proved request (docs/BENCHMARK_SPEC.md §14.2):
///
/// ```text
/// C = c_cpu·vcpus_p·T_prove + c_cpu·vcpus_p·T_prepare·/A
///   + N_v · ( c_cpu·vcpus_v·T_verify + (c_bw + c_store)·proof_bytes )
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct PriceModel {
    /// `arena-price-model-v1`.
    pub schema: String,
    pub id: String,
    pub version: u32,
    /// `draft` (never pinned by a signed challenge) or `governed`.
    pub status: String,
    pub effective_from: String,
    /// `USD`.
    pub currency: String,
    /// `femto_usd`.
    pub unit: String,
    /// `N_v`: validators that each verify every chunk's proof (stateless
    /// validation fan-out). ≥ 1.
    pub validators_per_chunk: u32,
    /// vCPUs of the reference validator profile; `verify` is measured pinned
    /// to this many of the benchmark CPUs and charged for them. ≥ 1 and ≤
    /// the challenge's `hardware_profile.vcpus`.
    pub verifier_vcpus: u32,
    /// `c_cpu`: price of one vCPU for one second (prover and validator).
    pub cpu_fusd_per_vcpu_second: u64,
    /// `c_bw`: network cost per proof byte per validator.
    pub bandwidth_fusd_per_byte: u64,
    /// `c_store`: retention cost per proof byte per validator (0 = none).
    pub storage_fusd_per_byte: u64,
    /// `A`: requests over which one `prepare` is amortized; 0 = `prepare`
    /// is not charged (reported only, bench-spec-v1 §2).
    pub prepare_amortization_requests: u64,
    pub rationale: Vec<PriceRationale>,
}

impl PriceModel {
    pub fn digest(&self) -> Result<Digest, canonical::CanonicalError> {
        canonical::sha256_digest(self)
    }
    /// Structural checks (not economics).
    pub fn validate(&self) -> Result<(), String> {
        if self.schema != PRICE_MODEL_SCHEMA {
            return Err(format!("price model schema {:?}", self.schema));
        }
        if self.unit != PRICE_MODEL_UNIT || self.currency != "USD" {
            return Err("price model unit must be femto_usd in USD".into());
        }
        if !matches!(self.status.as_str(), "draft" | "governed") {
            return Err(format!("price model status {:?}", self.status));
        }
        if self.id.is_empty() || self.version == 0 {
            return Err("price model needs an id and version >= 1".into());
        }
        if self.validators_per_chunk == 0 || self.verifier_vcpus == 0 {
            return Err("validators_per_chunk and verifier_vcpus must be >= 1".into());
        }
        if self.cpu_fusd_per_vcpu_second == 0 {
            return Err("cpu_fusd_per_vcpu_second must be > 0".into());
        }
        Ok(())
    }
}

/// Reference-candidate cost components of one class, measured under the
/// challenge's procedure (component medians over measured runs; one run =
/// one batch of `batch_size` requests).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CostBaselineClass {
    pub class_id: String,
    /// Median Σ prove wall ns per batch; must equal `workload_suite.baseline_ns`.
    pub prove_ns: u64,
    /// Median Σ verify wall ns per batch, on `verifier_vcpus` CPUs.
    pub verify_ns: u64,
    /// Median Σ proof bytes per batch.
    pub proof_bytes: u64,
}

/// `ChallengeDefinition.scoring` (v1.5, additive).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ScoringSpec {
    pub kind: ScoringKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub price_model: Option<PriceModel>,
    /// JCS sha256 of `price_model`; shown on every cost-board row.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub price_model_digest: Option<Digest>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub cost_baseline: Vec<CostBaselineClass>,
    /// Reference candidate's `prepare` wall ns (only charged when
    /// `prepare_amortization_requests > 0`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cost_baseline_prepare_ns: Option<u64>,
}

impl ScoringSpec {
    /// Consistency with the challenge it is part of.
    pub fn validate(&self, chal: &crate::ChallengeDefinition) -> Result<(), String> {
        match self.kind {
            ScoringKind::Speed => {
                if self.price_model.is_some()
                    || self.price_model_digest.is_some()
                    || !self.cost_baseline.is_empty()
                    || self.cost_baseline_prepare_ns.is_some()
                {
                    return Err("scoring.kind = speed takes no price model or cost baseline".into());
                }
                Ok(())
            }
            ScoringKind::CostV1 => {
                let pm = self
                    .price_model
                    .as_ref()
                    .ok_or("cost_v1 needs scoring.price_model")?;
                pm.validate()?;
                let d = pm.digest().map_err(|e| e.to_string())?;
                if self.price_model_digest.as_ref() != Some(&d) {
                    return Err(format!(
                        "scoring.price_model_digest != JCS digest of price_model ({d})"
                    ));
                }
                if pm.verifier_vcpus > chal.hardware_profile.vcpus {
                    return Err("price_model.verifier_vcpus > hardware_profile.vcpus".into());
                }
                if chal.tier == crate::challenge::Tier::Formal && pm.status != "governed" {
                    return Err("a formal challenge must pin a governed price model".into());
                }
                let base: std::collections::HashMap<&str, u64> = chal
                    .workload_suite
                    .baseline_ns
                    .iter()
                    .map(|(k, v)| (k.as_str(), *v))
                    .collect();
                if self.cost_baseline.len() != chal.workload_suite.classes.len() {
                    return Err("scoring.cost_baseline must list every workload class once".into());
                }
                for c in &chal.workload_suite.classes {
                    let Some(b) = self.cost_baseline.iter().find(|b| b.class_id == c.id) else {
                        return Err(format!("scoring.cost_baseline lacks class {:?}", c.id));
                    };
                    if base.get(c.id.as_str()) != Some(&b.prove_ns) {
                        return Err(format!(
                            "class {:?}: cost_baseline.prove_ns != workload_suite.baseline_ns",
                            c.id
                        ));
                    }
                    if b.prove_ns == 0 || b.verify_ns == 0 {
                        return Err(format!("class {:?}: zero baseline time", c.id));
                    }
                }
                if pm.prepare_amortization_requests > 0 && self.cost_baseline_prepare_ns.is_none() {
                    return Err("prepare is amortized: cost_baseline_prepare_ns required".into());
                }
                Ok(())
            }
        }
    }
}

/// Cost components of one class (component medians, integer femto-USD per
/// batch run). `*_fusd` validator terms already include the `N_v` factor.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct CostClass {
    pub class_id: String,
    pub weight_ppm: u32,
    pub prove_ns: u64,
    pub verify_ns: u64,
    pub proof_bytes: u64,
    pub prove_fusd: u64,
    pub prepare_fusd: u64,
    pub verify_fusd: u64,
    pub bandwidth_fusd: u64,
    pub storage_fusd: u64,
    pub total_fusd: u64,
    pub baseline_total_fusd: u64,
}

/// `BenchmarkResult.cost` (v1.5, additive): the cost-board result.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct CostResult {
    pub kind: ScoringKind,
    pub price_model_id: String,
    pub price_model_digest: Digest,
    pub validators_per_chunk: u32,
    pub verifier_vcpus: u32,
    pub score_milli: Option<u64>,
    pub score_ci_milli: Option<u64>,
    pub classes: Vec<CostClass>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ChallengeDefinition;

    const DRAFT: &str =
        include_str!("../../../challenges/price-models/pm-near-mainnet-2026q4.draft.json");

    fn v1_6() -> ChallengeDefinition {
        serde_json::from_str(include_str!(
            "../../../challenges/chl_7c0456cb2d1a36f8601863ac206cfcc9.json"
        ))
        .unwrap()
    }

    fn cost_spec(chal: &ChallengeDefinition, pm: PriceModel) -> ScoringSpec {
        ScoringSpec {
            kind: ScoringKind::CostV1,
            price_model_digest: Some(pm.digest().unwrap()),
            price_model: Some(pm),
            cost_baseline: chal
                .workload_suite
                .baseline_ns
                .iter()
                .map(|(c, ns)| CostBaselineClass {
                    class_id: c.clone(),
                    prove_ns: *ns,
                    verify_ns: 1,
                    proof_bytes: 1,
                })
                .collect(),
            cost_baseline_prepare_ns: None,
        }
    }

    #[test]
    fn draft_price_model_parses_validates_and_matches_python_jcs() {
        let pm: PriceModel = serde_json::from_str(DRAFT).unwrap();
        pm.validate().unwrap();
        assert_eq!(pm.status, "draft");
        // The offline re-scoring (Python JCS) records the same digest.
        let r: serde_json::Value = serde_json::from_str(include_str!(
            "../../../benchmarks/results/cost-rescore-v1-6-draft-20261005/rescore.json"
        ))
        .unwrap();
        assert_eq!(r["price_model_digest"], pm.digest().unwrap().as_str());
    }

    #[test]
    fn scoring_section_is_additive_and_checked() {
        let chal = v1_6();
        // Absent: speed, and the id is unchanged by the new optional field.
        assert_eq!(chal.scoring_kind(), ScoringKind::Speed);
        assert_eq!(chal.id().unwrap(), "chl_7c0456cb2d1a36f8601863ac206cfcc9");
        chal.check_scoring().unwrap();

        let pm: PriceModel = serde_json::from_str(DRAFT).unwrap();
        let mut c = chal.clone();
        c.scoring = Some(cost_spec(&chal, pm.clone()));
        // formal tier refuses a draft price model
        assert!(c.check_scoring().unwrap_err().contains("governed"));
        let mut gov = pm.clone();
        gov.status = "governed".into();
        c.scoring = Some(cost_spec(&chal, gov.clone()));
        c.check_scoring().unwrap();
        assert_eq!(c.scoring_kind(), ScoringKind::CostV1);
        assert_ne!(c.id().unwrap(), chal.id().unwrap());

        // digest must match the inline model
        let mut bad = cost_spec(&chal, gov.clone());
        bad.price_model.as_mut().unwrap().validators_per_chunk += 1;
        c.scoring = Some(bad);
        assert!(c.check_scoring().unwrap_err().contains("digest"));
        // baseline prove_ns must equal the frozen speed baseline
        let mut bad = cost_spec(&chal, gov.clone());
        bad.cost_baseline[0].prove_ns += 1;
        c.scoring = Some(bad);
        assert!(c.check_scoring().is_err());
        // a missing class
        let mut bad = cost_spec(&chal, gov.clone());
        bad.cost_baseline.pop();
        c.scoring = Some(bad);
        assert!(c.check_scoring().is_err());
        // verifier profile larger than the hardware profile
        let mut big = gov.clone();
        big.verifier_vcpus = chal.hardware_profile.vcpus + 1;
        c.scoring = Some(cost_spec(&chal, big));
        assert!(c.check_scoring().is_err());
        // speed with a price model
        let mut s = cost_spec(&chal, gov);
        s.kind = ScoringKind::Speed;
        c.scoring = Some(s);
        assert!(c.check_scoring().is_err());
    }
}
