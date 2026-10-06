//! Judge-side construction of the expected theorem type.
//!
//! The judge writes a generated Lean module (default `ArenaExpected`) that
//! defines `ArenaExpected.expectedType : Prop` from a *template* (owned by the
//! formal-core / challenge) and *data* (frozen challenge parameters and
//! artifact digests). The construction is pluggable (`ExpectedTypeBuilder`)
//! because formal-core's `AdmissionStatement` is still evolving.

use arena_types::Digest;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub trait ExpectedTypeBuilder: Send + Sync {
    /// Module name of the generated file (e.g. `ArenaExpected`).
    fn module_name(&self) -> &str;
    /// Fully qualified name of the definition holding the expected type.
    fn decl_name(&self) -> &str;
    /// Full Lean source of the generated module.
    fn render(&self) -> Result<String, ExpectedError> {
        self.render_with(&BTreeMap::new())
    }
    /// Render with judge-computed extra data (e.g. the digest of the judge's
    /// native verifier build for the `native-lean` route).
    fn render_with(&self, extra: &BTreeMap<String, LeanValue>) -> Result<String, ExpectedError>;
    /// Approved-interpreter route: hex sha256 of the verifier bytecode the
    /// statement pins as `.interp d`, if this statement is of that shape.
    fn interp_verifier_digest(&self) -> Option<String> {
        None
    }
    /// Digest identifying template + static data (for cache keys).
    fn identity(&self) -> Digest;
}

#[derive(Debug, thiserror::Error)]
pub enum ExpectedError {
    #[error("template placeholder {{{{{0}}}}} has no data")]
    MissingData(String),
    #[error("data key {0} is not used by the template")]
    UnusedData(String),
    #[error("invalid value for {0}: {1}")]
    BadValue(String, String),
    #[error("unterminated placeholder")]
    Unterminated,
}

/// A typed literal spliced into the template. Values are rendered as Lean
/// literals only — never as raw Lean syntax — so data cannot inject code.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", content = "value", rename_all = "snake_case")]
pub enum LeanValue {
    /// Natural number, decimal string (arbitrary size).
    Nat(String),
    /// String literal.
    Str(String),
    /// `sha256:<hex>` digest rendered as a string literal.
    Digest(Digest),
    /// Byte string given as lowercase hex, rendered as a list literal
    /// `[0x57, 0x74, …]` (e.g. formal-core's `Digest := List UInt8`).
    Bytes(String),
    /// A coverage tier id (contracts v1.7, CONTRACTS §11), rendered as the
    /// constructor of `NearSpecV3.Tier` from a fixed table ([`COVERAGE_TIERS`]);
    /// any other id is rejected, so this never splices free-form syntax.
    CoverageTier(String),
}

/// Declared tier id → `NearSpecV3.Tier` constructor (`near-chunk-v3`,
/// `spec/lean/v3/NearSpecV3/ChallengeChunkV3.lean`).
pub const COVERAGE_TIERS: &[(&str, &str)] = &[
    ("D0", "NearSpecV3.Tier.d0"),
    ("D1", "NearSpecV3.Tier.d1"),
    ("D2", "NearSpecV3.Tier.d2"),
    ("D3a", "NearSpecV3.Tier.d3a"),
];

impl LeanValue {
    pub fn render(&self, key: &str) -> Result<String, ExpectedError> {
        match self {
            LeanValue::Nat(s) => {
                if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
                    return Err(ExpectedError::BadValue(
                        key.into(),
                        "not a decimal natural".into(),
                    ));
                }
                Ok(format!("({s} : Nat)"))
            }
            LeanValue::Str(s) => lean_string(key, s),
            LeanValue::Digest(d) => lean_string(key, d.as_str()),
            LeanValue::CoverageTier(t) => COVERAGE_TIERS
                .iter()
                .find(|(id, _)| id == t)
                .map(|(_, c)| c.to_string())
                .ok_or_else(|| {
                    ExpectedError::BadValue(key.into(), format!("unknown coverage tier {t:?}"))
                }),
            LeanValue::Bytes(h) => {
                let b = hex::decode(h)
                    .map_err(|_| ExpectedError::BadValue(key.into(), "bytes must be hex".into()))?;
                Ok(format!(
                    "[{}]",
                    b.iter()
                        .map(|x| format!("0x{x:02x}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                ))
            }
        }
    }
}

fn lean_string(key: &str, s: &str) -> Result<String, ExpectedError> {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (' '..='~').contains(&c) => out.push(c),
            _ => {
                return Err(ExpectedError::BadValue(
                    key.into(),
                    "only printable ASCII strings".into(),
                ))
            }
        }
    }
    out.push('"');
    Ok(out)
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TemplateExpected {
    pub module: String,
    pub decl: String,
    /// Lean source with `{{key}}` placeholders.
    pub template: String,
    pub data: BTreeMap<String, LeanValue>,
}

impl ExpectedTypeBuilder for TemplateExpected {
    fn module_name(&self) -> &str {
        &self.module
    }
    fn decl_name(&self) -> &str {
        &self.decl
    }
    fn identity(&self) -> Digest {
        crate::digest::json_digest(self)
    }
    fn interp_verifier_digest(&self) -> Option<String> {
        if !self.template.contains(".interp {{verifier_digest}}")
            && !self.template.contains(".interp verifierDigest")
        {
            return None;
        }
        match self.data.get("verifier_digest") {
            Some(LeanValue::Bytes(h)) => Some(h.clone()),
            _ => None,
        }
    }
    fn render_with(&self, extra: &BTreeMap<String, LeanValue>) -> Result<String, ExpectedError> {
        let mut data = self.data.clone();
        for (k, v) in extra {
            data.insert(k.clone(), v.clone());
        }
        let mut out = String::new();
        let mut used = std::collections::BTreeSet::new();
        let mut rest = self.template.as_str();
        while let Some(i) = rest.find("{{") {
            out.push_str(&rest[..i]);
            let after = &rest[i + 2..];
            let j = after.find("}}").ok_or(ExpectedError::Unterminated)?;
            let key = after[..j].trim();
            let v = data
                .get(key)
                .ok_or_else(|| ExpectedError::MissingData(key.into()))?;
            out.push_str(&v.render(key)?);
            used.insert(key.to_string());
            rest = &after[j + 2..];
        }
        out.push_str(rest);
        if let Some(k) = data.keys().find(|k| !used.contains(*k)) {
            return Err(ExpectedError::UnusedData(k.clone()));
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn renders_literals_only() {
        let t = TemplateExpected {
            module: "ArenaExpected".into(),
            decl: "ArenaExpected.expectedType".into(),
            template: "def ArenaExpected.expectedType : Prop := P {{a}} {{b}}".into(),
            data: [
                ("a".into(), LeanValue::Nat("80".into())),
                ("b".into(), LeanValue::Str("x\"y".into())),
            ]
            .into(),
        };
        assert_eq!(
            t.render().unwrap(),
            "def ArenaExpected.expectedType : Prop := P (80 : Nat) \"x\\\"y\""
        );
        let mut bad = t.clone();
        bad.data
            .insert("a".into(), LeanValue::Nat("1) (sorry".into()));
        assert!(bad.render().is_err());
    }
}

#[cfg(test)]
mod interp_digest_tests {
    use super::*;

    fn t(template: &str, d: Option<&str>) -> TemplateExpected {
        TemplateExpected {
            module: "ArenaExpected".into(),
            decl: "ArenaExpected.expectedType".into(),
            template: template.into(),
            data: d
                .map(|h| {
                    BTreeMap::from([("verifier_digest".to_string(), LeanValue::Bytes(h.into()))])
                })
                .unwrap_or_default(),
        }
    }

    #[test]
    fn interp_digest_only_for_interp_statements() {
        let h = "ab".repeat(32);
        assert_eq!(
            t("impl := .interp verifierDigest", Some(&h)).interp_verifier_digest(),
            Some(h.clone())
        );
        assert_eq!(
            t("impl := .nativeTrusted x y z", Some(&h)).interp_verifier_digest(),
            None
        );
        assert_eq!(
            t("impl := .interp verifierDigest", None).interp_verifier_digest(),
            None
        );
    }
}
