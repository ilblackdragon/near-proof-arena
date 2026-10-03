//! Loading of governed files under `security/` (profiles and assumptions).
//!
//! Every file is parsed through `arena-types` (which uses
//! `deny_unknown_fields`), the `id` must equal the file stem, ids must be
//! unique, and every assumption referenced by a profile must exist.

use anyhow::{bail, Context, Result};
use arena_types::security::{Assumption, SecurityProfile};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Default)]
pub struct GovernedSet {
    pub profiles: BTreeMap<String, SecurityProfile>,
    pub assumptions: BTreeMap<String, Assumption>,
}

fn json_files(dir: &Path) -> Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    for e in fs::read_dir(dir).with_context(|| format!("reading {}", dir.display()))? {
        let p = e?.path();
        if p.extension().and_then(|x| x.to_str()) == Some("json") {
            out.push(p);
        }
    }
    out.sort();
    Ok(out)
}

fn stem(p: &Path) -> String {
    p.file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or_default()
        .to_string()
}

fn valid_id(id: &str) -> bool {
    !id.is_empty()
        && id.len() <= 64
        && id
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
}

impl GovernedSet {
    pub fn load(security_dir: &Path) -> Result<Self> {
        let mut set = GovernedSet::default();
        for p in json_files(&security_dir.join("assumptions"))? {
            let text = fs::read_to_string(&p)?;
            let a: Assumption = serde_json::from_str(&text)
                .with_context(|| format!("{}: not a valid Assumption", p.display()))?;
            if a.id != stem(&p) || !valid_id(&a.id) {
                bail!(
                    "{}: id {:?} must equal file stem and match [a-z0-9-]+",
                    p.display(),
                    a.id
                );
            }
            if !a.lean_decl.contains('.') || a.lean_decl.contains(char::is_whitespace) {
                bail!(
                    "{}: lean_decl must be a fully qualified Lean name",
                    p.display()
                );
            }
            if a.description.trim().is_empty() || a.references.is_empty() {
                bail!("{}: description and references are mandatory", p.display());
            }
            if set.assumptions.insert(a.id.clone(), a).is_some() {
                bail!("{}: duplicate assumption id", p.display());
            }
        }
        for p in json_files(&security_dir.join("profiles"))? {
            let text = fs::read_to_string(&p)?;
            let prof: SecurityProfile = serde_json::from_str(&text)
                .with_context(|| format!("{}: not a valid SecurityProfile", p.display()))?;
            if prof.id != stem(&p) || !valid_id(&prof.id) {
                bail!("{}: id {:?} must equal file stem", p.display(), prof.id);
            }
            if prof.target_bits < 80 {
                bail!("{}: target_bits below 80 is never governed", p.display());
            }
            for a in &prof.allowed_assumptions {
                if !set.assumptions.contains_key(a) {
                    bail!(
                        "{}: allowed assumption {a:?} is not a governed assumption",
                        p.display()
                    );
                }
            }
            let mut sorted = prof.allowed_assumptions.clone();
            sorted.sort();
            sorted.dedup();
            if sorted.len() != prof.allowed_assumptions.len() {
                bail!("{}: duplicate allowed_assumptions", p.display());
            }
            if set.profiles.insert(prof.id.clone(), prof).is_some() {
                bail!("{}: duplicate profile id", p.display());
            }
        }
        if set.profiles.is_empty() {
            bail!(
                "no security profiles found under {}",
                security_dir.display()
            );
        }
        Ok(set)
    }
}
