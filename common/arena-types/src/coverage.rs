//! Coverage-tiered challenges (contracts v1.7, docs/CONTRACTS.md §11,
//! docs/BENCHMARK_SPEC.md §17; first user `near-chunk-v3`).
//!
//! A coverage-tiered challenge has one statement (`statement_spec`) and a
//! total order of tiers. A candidate declares the tier it is complete for
//! (`candidate.toml [entry] declared_tier`), is admitted under that tier's
//! `params`, may abstain (`prove` exit 3, `UNSUPPORTED`) outside it, and is
//! ranked by tier rank first, then by score.

use crate::challenge::ChallengeDefinition;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub const COVERAGE_VERSION: &str = "coverage-v1";

/// `prove` exit code meaning `UNSUPPORTED` (abstain: the witness is outside
/// the declared tier). Only meaningful on challenges with `coverage`.
pub const PROVE_EXIT_UNSUPPORTED: i32 = 3;

/// `ChallengeDefinition.coverage`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CoverageSpec {
    /// `"coverage-v1"`.
    pub version: String,
    /// Lean declaration of the top `ChallengeSpec` (the statement every
    /// admitted verifier is sound for), e.g. `NearSpecV3.challengeSpecChunkTop`.
    pub statement_spec: String,
    /// Trusted Lean lemma lifting tier soundness to the statement, e.g.
    /// `NearSpecV3.sound_lift`.
    pub soundness_lift: String,
    /// Tiers in any order; `rank` is the total order (higher = larger domain).
    pub tiers: Vec<CoverageTier>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CoverageTier {
    /// Tier id, e.g. `D0`, `D1`, `D2`, `D3a`.
    pub id: String,
    pub rank: u32,
    /// Lean declaration (term) of the tier's `ChallengeParams`, e.g.
    /// `NearSpecV3.challengeParamsChunk .d0`. The judge's per-tier Expected
    /// template (formal-checker config `tiers`) instantiates exactly this.
    pub params: String,
    /// Workload classes this tier is complete for: an abstention on a
    /// positive case of one of them is `COVERAGE_GAP_IN_TIER`.
    pub classes: Vec<String>,
}

fn is_tier_id(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 32
        && s.bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_' || b == b'.')
}

impl CoverageSpec {
    pub fn tier(&self, id: &str) -> Option<&CoverageTier> {
        self.tiers.iter().find(|t| t.id == id)
    }

    /// Structural checks against the challenge it belongs to.
    pub fn validate(&self, chal: &ChallengeDefinition) -> Result<(), String> {
        if self.version != COVERAGE_VERSION {
            return Err(format!("coverage.version must be {COVERAGE_VERSION:?}"));
        }
        if self.statement_spec.is_empty() || self.soundness_lift.is_empty() {
            return Err("coverage.statement_spec and soundness_lift are required".into());
        }
        if self.tiers.is_empty() {
            return Err("coverage.tiers is empty".into());
        }
        let classes: Vec<&str> = chal
            .workload_suite
            .classes
            .iter()
            .map(|c| c.id.as_str())
            .collect();
        let mut ids = std::collections::BTreeSet::new();
        let mut ranks = std::collections::BTreeSet::new();
        for t in &self.tiers {
            if !is_tier_id(&t.id) {
                return Err(format!(
                    "coverage tier id {:?} is not [A-Za-z0-9._-]{{1,32}}",
                    t.id
                ));
            }
            if !ids.insert(t.id.as_str()) {
                return Err(format!("duplicate coverage tier {:?}", t.id));
            }
            if !ranks.insert(t.rank) {
                return Err(format!("duplicate coverage tier rank {}", t.rank));
            }
            if t.params.is_empty() {
                return Err(format!("coverage tier {:?} has no params", t.id));
            }
            for c in &t.classes {
                if !classes.contains(&c.as_str()) {
                    return Err(format!(
                        "coverage tier {:?} lists unknown workload class {c:?}",
                        t.id
                    ));
                }
            }
        }
        // A larger domain is complete for at least the classes of a smaller one.
        let mut by_rank: Vec<&CoverageTier> = self.tiers.iter().collect();
        by_rank.sort_by_key(|t| t.rank);
        for w in by_rank.windows(2) {
            if let Some(c) = w[0].classes.iter().find(|c| !w[1].classes.contains(c)) {
                return Err(format!(
                    "coverage tier {:?} (rank {}) omits class {c:?} of lower tier {:?}",
                    w[1].id, w[1].rank, w[0].id
                ));
            }
        }
        Ok(())
    }
}

/// Per-class tally of positive cases.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ClassCoverage {
    pub cases: u32,
    /// Proved and accepted by `verify`.
    pub proven: u32,
    /// `prove` answered `UNSUPPORTED`.
    pub abstained: u32,
}

/// One case set (conformance or held-out).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CoverageSection {
    /// Keyed by workload class id; public fixtures without a class are
    /// tallied under [`FIXTURES_KEY`] (not a class: excluded from `share_ppm`).
    pub per_class: BTreeMap<String, ClassCoverage>,
    /// Weight-averaged proven fraction over the challenge's workload classes,
    /// in parts per million (contracts carry no floating point).
    pub share_ppm: u32,
}

pub const FIXTURES_KEY: &str = "public-fixtures";

/// Report field `coverage` (CONTRACTS §11).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CoverageReport {
    /// The declared tier.
    pub tier: String,
    /// Public fixtures and judge-sampled cases.
    pub conformance: CoverageSection,
    /// Committed held-out cases (absent when the worker ran none).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub heldout: Option<CoverageSection>,
}

impl CoverageSection {
    /// Record one positive case outcome.
    pub fn record(&mut self, class: Option<&str>, proven: bool, abstained: bool) {
        let e = self
            .per_class
            .entry(class.unwrap_or(FIXTURES_KEY).to_string())
            .or_default();
        e.cases += 1;
        e.proven += u32::from(proven);
        e.abstained += u32::from(abstained);
    }

    /// Recompute `share_ppm` from `per_class` and the challenge's class weights:
    /// `Σ_c w_c · proven_c / cases_c` over classes with cases, renormalized by
    /// the weight of those classes.
    pub fn finish(&mut self, chal: &ChallengeDefinition) {
        let mut num = 0u128;
        let mut den = 0u128;
        for c in &chal.workload_suite.classes {
            if let Some(x) = self.per_class.get(&c.id).filter(|x| x.cases > 0) {
                num += c.weight_ppm as u128 * x.proven as u128 * 1_000_000 / x.cases as u128;
                den += c.weight_ppm as u128;
            }
        }
        self.share_ppm = num.checked_div(den).map_or(0, |x| x as u32);
    }
}

/// Renormalize weights (ppm) to sum exactly 1_000_000 (largest remainder,
/// ties by position). `None` if every weight is 0.
pub fn renormalize_ppm(weights: &[u32]) -> Option<Vec<u32>> {
    let total: u64 = weights.iter().map(|&w| w as u64).sum();
    if total == 0 {
        return None;
    }
    let mut out: Vec<u32> = weights
        .iter()
        .map(|&w| (w as u64 * 1_000_000 / total) as u32)
        .collect();
    let mut rem: Vec<(u64, usize)> = weights
        .iter()
        .enumerate()
        .map(|(i, &w)| ((w as u64 * 1_000_000) % total, i))
        .collect();
    rem.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
    let short = 1_000_000 - out.iter().map(|&w| w as u64).sum::<u64>();
    for (_, i) in rem.into_iter().take(short as usize) {
        out[i] += 1;
    }
    Some(out)
}

/// The classes a candidate proved, with weights renormalized over them
/// (BENCHMARK_SPEC §17: abstained classes carry no time and are excluded from
/// the score). `None` if no class was proved.
pub fn proven_classes(classes: &[crate::ClassMeasurement]) -> Option<Vec<crate::ClassMeasurement>> {
    let kept: Vec<crate::ClassMeasurement> =
        classes.iter().filter(|c| !c.abstained).cloned().collect();
    let w = renormalize_ppm(&kept.iter().map(|c| c.weight_ppm).collect::<Vec<_>>())?;
    Some(
        kept.into_iter()
            .zip(w)
            .map(|(mut c, w)| {
                c.weight_ppm = w;
                c
            })
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn chal() -> ChallengeDefinition {
        let mut d: ChallengeDefinition = serde_json::from_str(include_str!(
            "../../../challenges/chl_4b4316516128000f129cff9b3ced8b51.json"
        ))
        .unwrap();
        d.coverage = Some(spec());
        d
    }

    fn spec() -> CoverageSpec {
        CoverageSpec {
            version: COVERAGE_VERSION.into(),
            statement_spec: "NearSpecV3.challengeSpecChunkTop".into(),
            soundness_lift: "NearSpecV3.sound_lift".into(),
            tiers: vec![
                CoverageTier {
                    id: "D0".into(),
                    rank: 0,
                    params: "NearSpecV3.challengeParamsChunk .d0".into(),
                    classes: vec!["d0-quiet".into()],
                },
                CoverageTier {
                    id: "D1".into(),
                    rank: 1,
                    params: "NearSpecV3.challengeParamsChunk .d1".into(),
                    classes: vec!["d0-quiet".into(), "d0-transfers".into()],
                },
            ],
        }
    }

    #[test]
    fn validates() {
        let c = chal();
        c.coverage.as_ref().unwrap().validate(&c).unwrap();
        let mut s = spec();
        s.tiers[1].classes = vec!["d0-transfers".into()];
        assert!(s.validate(&c).unwrap_err().contains("omits class"));
        let mut s = spec();
        s.tiers[1].rank = 0;
        assert!(s
            .validate(&c)
            .unwrap_err()
            .contains("duplicate coverage tier rank"));
        let mut s = spec();
        s.tiers[0].classes.push("nope".into());
        assert!(s.validate(&c).is_err());
        let mut s = spec();
        s.version = "coverage-v2".into();
        assert!(s.validate(&c).is_err());
    }

    #[test]
    fn absent_coverage_keeps_the_challenge_id() {
        let raw = include_str!("../../../challenges/chl_4b4316516128000f129cff9b3ced8b51.json");
        let d: ChallengeDefinition = serde_json::from_str(raw).unwrap();
        assert!(d.coverage.is_none());
        assert_eq!(d.id().unwrap(), "chl_4b4316516128000f129cff9b3ced8b51");
        let mut with = d.clone();
        with.coverage = Some(spec());
        assert_ne!(with.id().unwrap(), d.id().unwrap());
        let back: ChallengeDefinition =
            serde_json::from_str(&serde_json::to_string(&with).unwrap()).unwrap();
        assert_eq!(back, with);
    }

    #[test]
    fn declared_tier_required_iff_coverage() {
        let raw = include_str!("../../../examples/reexec-v3-d0/candidate.toml");
        let m = crate::CandidateManifest::parse(raw).unwrap();
        let c = chal();
        assert!(c.declared_tier(&m).unwrap_err().contains("required"));
        let with = crate::CandidateManifest::parse(&raw.replace(
            "verify_route = \"native-lean\"",
            "verify_route = \"native-lean\"\ndeclared_tier = \"D1\"",
        ))
        .unwrap();
        assert_eq!(with.entry.declared_tier.as_deref(), Some("D1"));
        assert_eq!(c.declared_tier(&with).unwrap().unwrap().rank, 1);
        let mut unknown = with.clone();
        unknown.entry.declared_tier = Some("D9".into());
        assert!(c.declared_tier(&unknown).is_err());
        let mut plain = c.clone();
        plain.coverage = None;
        assert!(plain.declared_tier(&m).unwrap().is_none());
        assert!(plain
            .declared_tier(&with)
            .unwrap_err()
            .contains("only valid"));
        // the manifest field is syntax-checked and serialized only when present
        assert!(crate::CandidateManifest::parse(&raw.replace(
            "verify_route = \"native-lean\"",
            "verify_route = \"native-lean\"\ndeclared_tier = \"D 1\""
        ))
        .is_err());
        assert!(!serde_json::to_string(&m).unwrap().contains("declared_tier"));
    }

    #[test]
    fn renormalizes_exactly() {
        assert_eq!(
            renormalize_ppm(&[200_000, 500_000]).unwrap(),
            vec![285_714, 714_286]
        );
        assert_eq!(
            renormalize_ppm(&[1, 1, 1]).unwrap().iter().sum::<u32>(),
            1_000_000
        );
        assert_eq!(renormalize_ppm(&[1_000_000]).unwrap(), vec![1_000_000]);
        assert!(renormalize_ppm(&[0, 0]).is_none());
    }

    #[test]
    fn share_is_weighted_over_classes_with_cases() {
        let c = chal();
        let w: BTreeMap<&str, u32> = c
            .workload_suite
            .classes
            .iter()
            .map(|x| (x.id.as_str(), x.weight_ppm))
            .collect();
        let mut s = CoverageSection::default();
        s.record(None, true, false); // fixture: not a class
        s.record(Some("d0-quiet"), true, false);
        s.record(Some("d0-transfers"), false, true);
        s.record(Some("d0-transfers"), true, false);
        s.finish(&c);
        let (wq, wt) = (w["d0-quiet"] as u128, w["d0-transfers"] as u128);
        let want = (wq * 1_000_000 + wt * 500_000) / (wq + wt);
        assert_eq!(s.share_ppm as u128, want);
        assert_eq!(s.per_class[FIXTURES_KEY].cases, 1);
        assert_eq!(s.per_class["d0-transfers"].abstained, 1);
    }
}
