//! Extraction of protocol-version facts from nearcore sources.
//!
//! This is a deliberately simple lexical scan of
//! `core/primitives-core/src/version.rs`. If the expected shapes are not
//! found the result carries `parse_errors`, and the report treats that as
//! "unknown" (REVALIDATION_REQUIRED), never as "no change".

use serde::Serialize;
use std::collections::BTreeMap;
use std::path::Path;

pub const VERSION_RS: &str = "core/primitives-core/src/version.rs";
pub const DB_METADATA_RS: &str = "core/store/src/db/metadata.rs";

#[derive(Clone, Debug, Default, Serialize, PartialEq)]
pub struct ProtocolFacts {
    /// Constant name -> right-hand-side expression (whitespace-normalised).
    pub constants: BTreeMap<String, String>,
    /// `ProtocolFeature` variant -> version from `protocol_version()` (None if unmapped).
    pub features: BTreeMap<String, Option<u32>>,
    pub db_constants: BTreeMap<String, String>,
    pub parse_errors: Vec<String>,
}

fn norm(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// `[pub] const NAME: Ty = <expr>;` for the given names.
fn consts(text: &str, names: &[&str]) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for name in names {
        for pat in [format!("pub const {name}:"), format!("const {name}:")] {
            if let Some(i) = text.find(&pat) {
                let rest = &text[i + pat.len()..];
                if let Some(eq) = rest.find('=') {
                    let rhs = &rest[eq + 1..];
                    let end = rhs.find(';').unwrap_or(rhs.len());
                    out.insert((*name).to_string(), norm(&rhs[..end]));
                    break;
                }
            }
        }
    }
    out
}

fn strip_comments(text: &str) -> String {
    text.lines()
        .map(|l| match l.find("//") {
            Some(i) => &l[..i],
            None => l,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn is_ident(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

pub fn parse(root: &Path) -> ProtocolFacts {
    let mut f = ProtocolFacts::default();
    let Ok(raw) = std::fs::read_to_string(root.join(VERSION_RS)) else {
        f.parse_errors.push(format!("{VERSION_RS} not found"));
        return f;
    };
    let text = strip_comments(&raw);
    f.constants = consts(
        &text,
        &[
            "STABLE_PROTOCOL_VERSION",
            "NIGHTLY_PROTOCOL_VERSION",
            "MIN_SUPPORTED_PROTOCOL_VERSION",
            "PROD_GENESIS_PROTOCOL_VERSION",
            "PROTOCOL_VERSION",
        ],
    );
    for n in ["STABLE_PROTOCOL_VERSION", "MIN_SUPPORTED_PROTOCOL_VERSION"] {
        if !f.constants.contains_key(n) {
            f.parse_errors.push(format!("constant {n} not found"));
        }
    }

    // enum variants
    let Some(ei) = text.find("pub enum ProtocolFeature") else {
        f.parse_errors.push("enum ProtocolFeature not found".into());
        return f;
    };
    let body_start = ei + text[ei..].find('{').unwrap_or(0) + 1;
    let mut depth = 1usize;
    let mut end = body_start;
    for (i, c) in text[body_start..].char_indices() {
        match c {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    end = body_start + i;
                    break;
                }
            }
            _ => {}
        }
    }
    let body = &text[body_start..end];
    // Drop attributes `#[...]` then split on commas.
    let mut cleaned = String::new();
    let mut chars = body.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '#' && chars.peek() == Some(&'[') {
            let mut d = 0;
            for c2 in chars.by_ref() {
                if c2 == '[' {
                    d += 1;
                } else if c2 == ']' {
                    d -= 1;
                    if d == 0 {
                        break;
                    }
                }
            }
        } else {
            cleaned.push(c);
        }
    }
    for item in cleaned.split(',') {
        let name: String = item.trim().chars().take_while(|c| is_ident(*c)).collect();
        if !name.is_empty() {
            f.features.insert(name, None);
        }
    }
    if f.features.is_empty() {
        f.parse_errors.push("no ProtocolFeature variants found".into());
    }

    // protocol_version() match arms
    let Some(fi) = text.find("fn protocol_version(self)") else {
        f.parse_errors.push("ProtocolFeature::protocol_version not found".into());
        return f;
    };
    let fn_text = &text[fi..];
    let fn_end = fn_text.find("pub const fn enabled").unwrap_or(fn_text.len());
    let fn_text = &fn_text[..fn_end];
    let mut pending: Vec<String> = Vec::new();
    let mut rest = fn_text;
    loop {
        let a = rest.find("ProtocolFeature::");
        let b = rest.find("=>");
        match (a, b) {
            (Some(a), Some(b)) if a < b => {
                let after = &rest[a + "ProtocolFeature::".len()..];
                let name: String = after.chars().take_while(|c| is_ident(*c)).collect();
                pending.push(name.clone());
                rest = &after[name.len()..];
            }
            (_, Some(b)) => {
                let after = rest[b + 2..].trim_start();
                let num: String = after.chars().take_while(|c| c.is_ascii_digit()).collect();
                let v = num.parse::<u32>().ok();
                if v.is_none() {
                    f.parse_errors.push(format!("non-literal version for {pending:?}"));
                }
                for p in pending.drain(..) {
                    f.features.insert(p, v);
                }
                rest = &rest[b + 2..];
            }
            _ => break,
        }
    }
    for (k, v) in &f.features {
        if v.is_none() {
            f.parse_errors.push(format!("feature {k} has no version mapping"));
        }
    }

    if let Ok(db) = std::fs::read_to_string(root.join(DB_METADATA_RS)) {
        f.db_constants = consts(&strip_comments(&db), &["DB_VERSION", "MIN_SUPPORTED_DB_VERSION"]);
    } else {
        f.parse_errors.push(format!("{DB_METADATA_RS} not found"));
    }
    f
}

pub fn stable_version(f: &ProtocolFacts) -> Option<u32> {
    f.constants.get("STABLE_PROTOCOL_VERSION").and_then(|s| s.parse().ok())
}

#[derive(Debug, Default, Serialize)]
pub struct ProtocolDiff {
    pub old_stable: Option<u32>,
    pub new_stable: Option<u32>,
    pub constants_changed: BTreeMap<String, (Option<String>, Option<String>)>,
    pub features_added: BTreeMap<String, Option<u32>>,
    pub features_removed: BTreeMap<String, Option<u32>>,
    pub features_version_changed: BTreeMap<String, (Option<u32>, Option<u32>)>,
    /// `X` renamed to `_DeprecatedX` at the same version (cleanup of an
    /// already-stable feature; the gate is removed from code paths).
    pub features_deprecated: Vec<String>,
    /// Features enabled at the new stable version but not at the old one.
    pub newly_stable_features: Vec<String>,
    pub db_constants_changed: BTreeMap<String, (Option<String>, Option<String>)>,
    pub parse_errors: Vec<String>,
}

impl ProtocolDiff {
    pub fn is_empty(&self) -> bool {
        self.constants_changed.is_empty()
            && self.features_added.is_empty()
            && self.features_removed.is_empty()
            && self.features_version_changed.is_empty()
            && self.features_deprecated.is_empty()
            && self.newly_stable_features.is_empty()
            && self.db_constants_changed.is_empty()
            && self.parse_errors.is_empty()
    }
}

fn map_diff(a: &BTreeMap<String, String>, b: &BTreeMap<String, String>) -> BTreeMap<String, (Option<String>, Option<String>)> {
    let mut out = BTreeMap::new();
    for k in a.keys().chain(b.keys()) {
        let (x, y) = (a.get(k).cloned(), b.get(k).cloned());
        if x != y {
            out.insert(k.clone(), (x, y));
        }
    }
    out
}

pub fn diff(old: &ProtocolFacts, new: &ProtocolFacts) -> ProtocolDiff {
    let mut d = ProtocolDiff {
        old_stable: stable_version(old),
        new_stable: stable_version(new),
        constants_changed: map_diff(&old.constants, &new.constants),
        db_constants_changed: map_diff(&old.db_constants, &new.db_constants),
        ..Default::default()
    };
    for e in &old.parse_errors {
        d.parse_errors.push(format!("old: {e}"));
    }
    for e in &new.parse_errors {
        d.parse_errors.push(format!("new: {e}"));
    }
    for (k, v) in &new.features {
        match old.features.get(k) {
            None => {
                d.features_added.insert(k.clone(), *v);
            }
            Some(ov) if ov != v => {
                d.features_version_changed.insert(k.clone(), (*ov, *v));
            }
            _ => {}
        }
    }
    for (k, v) in &old.features {
        if !new.features.contains_key(k) {
            d.features_removed.insert(k.clone(), *v);
        }
    }
    let renamed: Vec<String> = d
        .features_removed
        .iter()
        .filter(|(k, v)| d.features_added.get(&format!("_Deprecated{k}")) == Some(*v))
        .map(|(k, _)| k.clone())
        .collect();
    for k in &renamed {
        d.features_removed.remove(k);
        d.features_added.remove(&format!("_Deprecated{k}"));
    }
    d.features_deprecated = renamed;
    let enabled = |f: &ProtocolFacts, name: &str, at: Option<u32>| match (f.features.get(name), at) {
        (Some(Some(v)), Some(s)) => *v <= s,
        _ => false,
    };
    for k in new.features.keys() {
        let old_name = k.strip_prefix("_Deprecated").unwrap_or(k);
        if enabled(new, k, d.new_stable) && !enabled(old, k, d.old_stable) && !enabled(old, old_name, d.old_stable) {
            d.newly_stable_features.push(k.clone());
        }
    }
    d
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = r#"
pub enum ProtocolFeature {
    #[deprecated]
    _DeprecatedA,
    /// doc, with comma
    B,
    C, // trailing
}
impl ProtocolFeature {
    pub const fn protocol_version(self) -> ProtocolVersion {
        match self {
            ProtocolFeature::_DeprecatedA => 10,
            ProtocolFeature::B
            | ProtocolFeature::C => 12,
        }
    }
    pub const fn enabled(&self, protocol_version: ProtocolVersion) -> bool { true }
}
pub const MIN_SUPPORTED_PROTOCOL_VERSION: ProtocolVersion = 9;
const STABLE_PROTOCOL_VERSION: ProtocolVersion = 12;
"#;

    fn facts(src: &str) -> ProtocolFacts {
        let t = tempfile::tempdir().unwrap();
        let p = t.path().join(VERSION_RS);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, src).unwrap();
        parse(t.path())
    }

    #[test]
    fn parses_features_and_versions() {
        let f = facts(SRC);
        assert_eq!(f.features.get("B"), Some(&Some(12)));
        assert_eq!(f.features.get("C"), Some(&Some(12)));
        assert_eq!(f.features.get("_DeprecatedA"), Some(&Some(10)));
        assert_eq!(f.features.len(), 3);
        assert_eq!(f.constants["STABLE_PROTOCOL_VERSION"], "12");
        // only the missing DB metadata file
        assert_eq!(f.parse_errors.len(), 1, "{:?}", f.parse_errors);
    }

    #[test]
    fn diff_detects_new_and_newly_stable() {
        let old = facts(SRC);
        let new_src = SRC
            .replace("C, // trailing", "C,\n    D,")
            .replace("ProtocolFeature::C => 12,", "ProtocolFeature::C => 12,\n ProtocolFeature::D => 13,")
            .replace("= 12;", "= 13;");
        let new = facts(&new_src);
        let d = diff(&old, &new);
        assert!(d.features_added.contains_key("D"));
        assert_eq!(d.newly_stable_features, vec!["D".to_string()]);
        assert_eq!(d.old_stable, Some(12));
        assert_eq!(d.new_stable, Some(13));
    }

    #[test]
    fn deprecation_rename_is_not_add_remove() {
        let old = facts(SRC);
        let new = facts(&SRC.replace("    B,", "    _DeprecatedB,").replace("ProtocolFeature::B\n", "ProtocolFeature::_DeprecatedB\n"));
        let d = diff(&old, &new);
        assert_eq!(d.features_deprecated, vec!["B".to_string()]);
        assert!(d.features_added.is_empty() && d.features_removed.is_empty());
        assert!(d.newly_stable_features.is_empty());
    }

    #[test]
    fn unparseable_is_reported() {
        let f = facts("fn main() {}");
        assert!(!f.parse_errors.is_empty());
    }
}
