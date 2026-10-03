//! Signed challenge files: `challenges/<id>.json` + `challenges/<id>.sig`.
//!
//! * `<id>.json` is the pretty-printed `ChallengeDefinition` with every field
//!   present (Options as explicit `null`). Readers parse it through
//!   `arena-types` (`deny_unknown_fields`) and re-canonicalize; the raw file
//!   must canonicalize to the same bytes as the typed value (so no field may
//!   be omitted, duplicated or reordered into a different meaning).
//! * `<id>.sig` is ed25519 over `JCS(definition)` as one line of hex.
//! * `<id>` = `ChallengeDefinition::id()`; the file name must match.

use crate::governed::GovernedSet;
use crate::keys::{Keypair, PublicKey};
use crate::policy::{self, Findings};
use anyhow::{bail, Context, Result};
use arena_types::challenge::{ChallengeDefinition, Tier};
use arena_types::{canonical_json, Digest};
use std::fs;
use std::path::{Path, PathBuf};

pub fn parse_definition(text: &str) -> Result<ChallengeDefinition> {
    let def: ChallengeDefinition = serde_json::from_str(text)
        .context("not a valid ChallengeDefinition (arena-types, deny_unknown_fields)")?;
    // Require the raw document to be exactly the typed value (no omitted
    // Option fields relying on defaults).
    let raw: serde_json::Value = serde_json::from_str(text)?;
    if canonical_json(&raw)? != canonical_json(&def)? {
        bail!("document is not in normal form: every field must be present explicitly (use null for absent options)");
    }
    Ok(def)
}

pub fn load_definition(path: &Path) -> Result<ChallengeDefinition> {
    let text = fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    parse_definition(&text).with_context(|| format!("{}", path.display()))
}

pub struct Identity {
    pub id: String,
    pub digest: Digest,
    pub jcs: Vec<u8>,
}

pub fn identity(def: &ChallengeDefinition) -> Result<Identity> {
    let jcs = canonical_json(def)?;
    Ok(Identity {
        id: def.id()?,
        digest: def.digest()?,
        jcs,
    })
}

pub fn paths_for(dir: &Path, id: &str) -> (PathBuf, PathBuf) {
    (
        dir.join(format!("{id}.json")),
        dir.join(format!("{id}.sig")),
    )
}

/// Policy-check, sign and write a challenge. Refuses to overwrite.
pub fn sign_and_write(
    def: &ChallengeDefinition,
    key: &Keypair,
    gov: &GovernedSet,
    dir: &Path,
) -> Result<(Identity, Findings)> {
    let findings = policy::check_definition(def, gov);
    if !findings.ok() {
        bail!(
            "policy check failed:\n  - {}",
            findings.errors.join("\n  - ")
        );
    }
    if def.tier == Tier::Formal && key.dev_only {
        bail!("refusing to sign a formal-tier challenge with a dev-only key");
    }
    let ident = identity(def)?;
    let (jp, sp) = paths_for(dir, &ident.id);
    if jp.exists() || sp.exists() {
        bail!("{} already exists; challenges are immutable", jp.display());
    }
    let sig = key.sign_hex(&ident.jcs);
    let mut pretty = serde_json::to_string_pretty(def)?;
    pretty.push('\n');
    fs::write(&jp, pretty)?;
    fs::write(&sp, format!("{sig}\n"))?;
    Ok((ident, findings))
}

#[derive(Debug)]
pub struct Verified {
    pub id: String,
    pub digest: Digest,
    pub def: ChallengeDefinition,
    pub findings: Findings,
}

/// Full verification of a challenge file: parse, id recomputation and file
/// name, detached signature, governed profile/assumptions, policy.
pub fn verify_file(path: &Path, keys: &[PublicKey], gov: &GovernedSet) -> Result<Verified> {
    let def = load_definition(path)?;
    let ident = identity(&def)?;
    let stem = path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or_default();
    if stem != ident.id {
        bail!(
            "{}: recomputed id {} does not match file name",
            path.display(),
            ident.id
        );
    }
    let sig_path = path.with_extension("sig");
    let sig =
        fs::read_to_string(&sig_path).with_context(|| format!("reading {}", sig_path.display()))?;
    let mut signer = None;
    for k in keys {
        if k.verify_hex(&ident.jcs, &sig).is_ok() {
            signer = Some(k);
            break;
        }
    }
    let Some(signer) = signer else {
        bail!(
            "{}: signature does not verify under any trusted governance key",
            path.display()
        );
    };
    let mut findings = policy::check_definition(&def, gov);
    if def.tier == Tier::Formal && signer.file.dev_only {
        findings.errors.push(format!(
            "formal-tier challenge signed by dev-only key {}",
            signer.file.key_id
        ));
    }
    if signer.file.dev_only {
        findings.warnings.push(format!(
            "signed by DEV-ONLY key {} — not for production",
            signer.file.key_id
        ));
    }
    if let Some(prev) = &def.supersedes {
        let (pj, _) = paths_for(path.parent().unwrap_or(Path::new(".")), prev);
        if !pj.exists() {
            findings.warnings.push(format!(
                "superseded challenge {prev} not present next to this file"
            ));
        }
    }
    if !findings.ok() {
        bail!(
            "{}: policy check failed:\n  - {}",
            path.display(),
            findings.errors.join("\n  - ")
        );
    }
    Ok(Verified {
        id: ident.id,
        digest: ident.digest,
        def,
        findings,
    })
}

/// Rules for a successor challenge (on top of the normal policy checks).
pub fn check_supersession(
    old: &ChallengeDefinition,
    old_id: &str,
    new: &ChallengeDefinition,
    allow_downgrade: bool,
) -> Findings {
    let mut f = Findings::default();
    if new.supersedes.as_deref() != Some(old_id) {
        f.errors
            .push(format!("new definition must set supersedes = {old_id:?}"));
    }
    let fmt = &time::format_description::well_known::Rfc3339;
    match (
        time::OffsetDateTime::parse(&old.created_at, fmt),
        time::OffsetDateTime::parse(&new.created_at, fmt),
    ) {
        (Ok(a), Ok(b)) if b > a => {}
        _ => f
            .errors
            .push("new created_at must be strictly later than the superseded challenge's".into()),
    }
    if new.protocol_version < old.protocol_version && !allow_downgrade {
        f.errors.push(format!(
            "protocol_version downgrade {} -> {} (pass --allow-downgrade with a recorded governance decision)",
            old.protocol_version, new.protocol_version
        ));
    }
    if new.name != old.name {
        f.warnings
            .push(format!("name changes {:?} -> {:?}", old.name, new.name));
    }
    if (new.tier as u8) != (old.tier as u8) {
        f.warnings
            .push(format!("tier changes {:?} -> {:?}", old.tier, new.tier));
    }
    f
}

/// `TreeDigest` per docs/CONTRACTS.md §1: JCS array of
/// `[relative_path, "file"|"exec", "sha256:<hex>"]` sorted by path bytes.
/// Rejects symlinks and non-regular files.
pub fn tree_digest(root: &Path) -> Result<Digest> {
    Ok(arena_types::tree_digest(root)?)
}
