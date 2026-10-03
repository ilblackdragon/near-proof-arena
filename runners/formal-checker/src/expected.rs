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
    fn render(&self) -> Result<String, ExpectedError>;
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
}

impl LeanValue {
    pub fn render(&self, key: &str) -> Result<String, ExpectedError> {
        match self {
            LeanValue::Nat(s) => {
                if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
                    return Err(ExpectedError::BadValue(key.into(), "not a decimal natural".into()));
                }
                Ok(format!("({s} : Nat)"))
            }
            LeanValue::Str(s) => lean_string(key, s),
            LeanValue::Digest(d) => lean_string(key, d.as_str()),
            LeanValue::Bytes(h) => {
                let b = hex::decode(h).map_err(|_| ExpectedError::BadValue(key.into(), "bytes must be hex".into()))?;
                Ok(format!("[{}]", b.iter().map(|x| format!("0x{x:02x}")).collect::<Vec<_>>().join(", ")))
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
            _ => return Err(ExpectedError::BadValue(key.into(), "only printable ASCII strings".into())),
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
    fn render(&self) -> Result<String, ExpectedError> {
        let mut out = String::new();
        let mut used = std::collections::BTreeSet::new();
        let mut rest = self.template.as_str();
        while let Some(i) = rest.find("{{") {
            out.push_str(&rest[..i]);
            let after = &rest[i + 2..];
            let j = after.find("}}").ok_or(ExpectedError::Unterminated)?;
            let key = after[..j].trim();
            let v = self.data.get(key).ok_or_else(|| ExpectedError::MissingData(key.into()))?;
            out.push_str(&v.render(key)?);
            used.insert(key.to_string());
            rest = &after[j + 2..];
        }
        out.push_str(rest);
        if let Some(k) = self.data.keys().find(|k| !used.contains(*k)) {
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
            data: [("a".into(), LeanValue::Nat("80".into())), ("b".into(), LeanValue::Str("x\"y".into()))].into(),
        };
        assert_eq!(t.render().unwrap(), "def ArenaExpected.expectedType : Prop := P (80 : Nat) \"x\\\"y\"");
        let mut bad = t.clone();
        bad.data.insert("a".into(), LeanValue::Nat("1) (sorry".into()));
        assert!(bad.render().is_err());
    }
}
