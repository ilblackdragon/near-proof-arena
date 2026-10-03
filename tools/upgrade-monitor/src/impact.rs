//! Governed mapping from nearcore paths to spec definitions, obligations and
//! fixtures (`spec/impact-map.toml`).

use anyhow::{bail, Context, Result};
use arena_types::ObligationId;
use globset::{GlobBuilder, GlobMatcher};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

pub const SCHEMA: &str = "arena-impact-map-v1";

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawMap {
    schema: String,
    default: Target,
    #[serde(default)]
    rule: Vec<RawRule>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Target {
    pub spec_definitions: Vec<String>,
    pub obligations: Vec<ObligationId>,
    pub fixtures: Vec<String>,
    #[serde(default)]
    pub note: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawRule {
    id: String,
    paths: Vec<String>,
    spec_definitions: Vec<String>,
    obligations: Vec<ObligationId>,
    fixtures: Vec<String>,
    #[serde(default)]
    note: String,
}

pub struct Rule {
    pub id: String,
    matchers: Vec<GlobMatcher>,
    pub target: Target,
}

pub struct ImpactMap {
    pub default: Target,
    pub rules: Vec<Rule>,
}

impl ImpactMap {
    pub fn load(path: &Path) -> Result<Self> {
        let text =
            std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
        Self::parse(&text)
    }

    pub fn parse(text: &str) -> Result<Self> {
        let raw: RawMap = toml::from_str(text).context("parsing impact map")?;
        if raw.schema != SCHEMA {
            bail!("impact map schema must be {SCHEMA:?}");
        }
        if raw.default.obligations.is_empty() {
            bail!("impact map [default] must reopen at least one obligation (fail closed)");
        }
        let mut ids = BTreeSet::new();
        let mut rules = Vec::new();
        for r in raw.rule {
            if !ids.insert(r.id.clone()) {
                bail!("duplicate impact rule id {:?}", r.id);
            }
            if r.paths.is_empty() {
                bail!("impact rule {:?} has no paths", r.id);
            }
            let matchers = r
                .paths
                .iter()
                .map(|g| {
                    GlobBuilder::new(g)
                        .literal_separator(true)
                        .build()
                        .map(|g| g.compile_matcher())
                        .with_context(|| format!("rule {}: bad glob {g:?}", r.id))
                })
                .collect::<Result<Vec<_>>>()?;
            let target = Target {
                spec_definitions: r.spec_definitions,
                obligations: r.obligations,
                fixtures: r.fixtures,
                note: r.note,
            };
            rules.push(Rule {
                id: r.id,
                matchers,
                target,
            });
        }
        Ok(ImpactMap {
            default: raw.default,
            rules,
        })
    }

    pub fn matching(&self, path: &str) -> Vec<&Rule> {
        self.rules
            .iter()
            .filter(|r| r.matchers.iter().any(|m| m.is_match(path)))
            .collect()
    }
}

#[derive(Debug, Default, Serialize)]
pub struct RuleHit {
    pub rule: String,
    pub files: Vec<String>,
    pub spec_definitions: Vec<String>,
    pub obligations: Vec<ObligationId>,
    pub fixtures: Vec<String>,
    pub note: String,
}

#[derive(Debug, Default, Serialize)]
pub struct Impact {
    pub rule_hits: Vec<RuleHit>,
    /// Changed closure files no rule matches; the `[default]` target applies.
    pub unmapped_files: Vec<String>,
    pub spec_definitions_to_revalidate: Vec<String>,
    pub obligations_to_reopen: Vec<ObligationId>,
    pub fixtures_to_regenerate: Vec<String>,
}

/// `files`: changed paths inside the semantic closure. Paths that matter but
/// are not files (parameter/protocol facts) are passed as pseudo-paths by the
/// caller (e.g. `@protocol-version`).
pub fn evaluate(map: &ImpactMap, files: &[String]) -> Impact {
    let mut hits: BTreeMap<String, RuleHit> = BTreeMap::new();
    let mut unmapped = Vec::new();
    for f in files {
        let rules = map.matching(f);
        if rules.is_empty() {
            unmapped.push(f.clone());
        }
        for r in rules {
            let h = hits.entry(r.id.clone()).or_insert_with(|| RuleHit {
                rule: r.id.clone(),
                spec_definitions: r.target.spec_definitions.clone(),
                obligations: r.target.obligations.clone(),
                fixtures: r.target.fixtures.clone(),
                note: r.target.note.clone(),
                ..Default::default()
            });
            h.files.push(f.clone());
        }
    }
    let mut specs = BTreeSet::new();
    let mut obls = BTreeSet::new();
    let mut fixtures = BTreeSet::new();
    let mut add = |t: &Target| {
        specs.extend(t.spec_definitions.iter().cloned());
        obls.extend(t.obligations.iter().copied());
        fixtures.extend(t.fixtures.iter().cloned());
    };
    for h in hits.values() {
        add(&Target {
            spec_definitions: h.spec_definitions.clone(),
            obligations: h.obligations.clone(),
            fixtures: h.fixtures.clone(),
            note: String::new(),
        });
    }
    if !unmapped.is_empty() {
        add(&map.default);
    }
    Impact {
        rule_hits: hits.into_values().collect(),
        unmapped_files: unmapped,
        spec_definitions_to_revalidate: specs.into_iter().collect(),
        obligations_to_reopen: obls.into_iter().collect(),
        fixtures_to_regenerate: fixtures.into_iter().collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const MAP: &str = r#"
schema = "arena-impact-map-v1"
[default]
spec_definitions = ["*"]
obligations = ["FORMAL_SEMANTIC_SOUNDNESS"]
fixtures = ["*"]
[[rule]]
id = "actions"
paths = ["runtime/runtime/src/actions.rs", "core/parameters/res/**"]
spec_definitions = ["NearSpec.applyAction"]
obligations = ["CONFORMANCE_DIFFERENTIAL"]
fixtures = ["oracle/fixtures/**"]
"#;

    #[test]
    fn globs_and_default() {
        let m = ImpactMap::parse(MAP).unwrap();
        let i = evaluate(
            &m,
            &[
                "runtime/runtime/src/actions.rs".into(),
                "core/parameters/res/runtime_configs/86.yaml".into(),
                "x/y.rs".into(),
            ],
        );
        assert_eq!(i.rule_hits.len(), 1);
        assert_eq!(i.rule_hits[0].files.len(), 2);
        assert_eq!(i.unmapped_files, vec!["x/y.rs".to_string()]);
        assert!(i
            .obligations_to_reopen
            .contains(&ObligationId::FormalSemanticSoundness));
        assert!(i
            .obligations_to_reopen
            .contains(&ObligationId::ConformanceDifferential));
    }

    #[test]
    fn star_does_not_cross_directories() {
        let m = ImpactMap::parse(&MAP.replace("core/parameters/res/**", "core/*.rs")).unwrap();
        assert!(m.matching("core/a/b.rs").is_empty());
        assert_eq!(m.matching("core/b.rs").len(), 1);
    }

    #[test]
    fn rejects_unknown_obligation_and_empty_default() {
        assert!(ImpactMap::parse(&MAP.replace("CONFORMANCE_DIFFERENTIAL", "MADE_UP")).is_err());
        assert!(ImpactMap::parse(&MAP.replace(
            r#"obligations = ["FORMAL_SEMANTIC_SOUNDNESS"]"#,
            "obligations = []"
        ))
        .is_err());
    }
}
