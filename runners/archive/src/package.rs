//! Candidate package layout + `candidate.toml` validation (CONTRACTS §3).
//!
//! All checks run against the [`Tree`] produced by ingestion, never against
//! the filesystem, and the manifest bytes are read from the extracted root
//! only after confirming (via the tree) that `candidate.toml` is a regular
//! file.

use crate::tree::Tree;
use arena_types::CandidateManifest;
use std::collections::BTreeSet;
use std::io::Read;
use std::path::Path;

pub const MANIFEST_PATH: &str = "candidate.toml";
pub const MAX_MANIFEST_BYTES: u64 = 64 * 1024;
pub const MAX_OUTPUTS: usize = 64;

/// Required top-level layout entries. Directories must exist (an empty
/// directory is fine; tar producers usually emit explicit entries).
pub const REQUIRED_DIRS: &[&str] = &["source", "dependency-locks", "build-recipe"];
pub const REQUIRED_FILES: &[&str] = &["README.md"];

#[derive(Debug, thiserror::Error)]
pub enum PackageError {
    /// Maps to `MANIFEST_INVALID`.
    #[error("manifest invalid: {0}")]
    Manifest(String),
    /// Layout problem (missing directory, non-executable recipe, ...).
    /// Also maps to `MANIFEST_INVALID`.
    #[error("package layout invalid: {0}")]
    Layout(String),
    /// Judge-side I/O. Maps to `INFRA_ERROR`.
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
}

fn layout(s: impl Into<String>) -> PackageError {
    PackageError::Layout(s.into())
}

/// Validate an extracted package rooted at `root` whose content is `tree`.
pub fn validate_package(root: &Path, tree: &Tree) -> Result<CandidateManifest, PackageError> {
    let Some(mf) = tree.files.get(MANIFEST_PATH) else {
        return Err(PackageError::Manifest("candidate.toml missing (or not a regular file)".into()));
    };
    if mf.size > MAX_MANIFEST_BYTES {
        return Err(PackageError::Manifest(format!("candidate.toml larger than {MAX_MANIFEST_BYTES} bytes")));
    }
    let mut bytes = Vec::new();
    crate::tree::open_nofollow(&root.join(MANIFEST_PATH))?.take(MAX_MANIFEST_BYTES + 1).read_to_end(&mut bytes)?;
    if arena_types::Digest::of_bytes(&bytes) != mf.digest {
        return Err(PackageError::Manifest("candidate.toml changed after extraction".into()));
    }
    let text = std::str::from_utf8(&bytes).map_err(|_| PackageError::Manifest("candidate.toml is not UTF-8".into()))?;
    let m = CandidateManifest::parse(text).map_err(|e| PackageError::Manifest(e.to_string()))?;
    validate_layout(&m, tree)?;
    Ok(m)
}

/// Layout rules beyond the manifest schema:
///
/// * `README.md` is a file; `source/`, `dependency-locks/`, `build-recipe/`
///   are directories; `formal.lean_project` is a directory when present.
/// * `build.recipe` is an executable regular file under `build-recipe/`.
/// * `build.outputs` is non-empty, at most 64 entries, unique, pairwise
///   non-nested, and none of them exists in the package (the judge builds
///   them; shipping them pre-built is refused).
/// * every `entry.*` path is one of `build.outputs` or lies beneath one.
pub fn validate_layout(m: &CandidateManifest, tree: &Tree) -> Result<(), PackageError> {
    for f in REQUIRED_FILES {
        if !tree.is_file(f) {
            return Err(layout(format!("{f} missing")));
        }
    }
    for d in REQUIRED_DIRS {
        if !tree.is_dir(d) {
            return Err(layout(format!("{d}/ missing")));
        }
    }
    if let Some(formal) = &m.formal {
        if !tree.is_dir(&formal.lean_project) {
            return Err(layout(format!("formal.lean_project {:?} is not a directory", formal.lean_project)));
        }
        if formal.certificate.is_empty() || formal.certificate.len() > 255 {
            return Err(layout("formal.certificate must be a non-empty Lean name"));
        }
    }
    let recipe = &m.build.recipe;
    if !recipe.starts_with("build-recipe/") {
        return Err(layout("build.recipe must live under build-recipe/"));
    }
    if !tree.is_file(recipe) {
        return Err(layout(format!("build.recipe {recipe:?} is not a regular file")));
    }
    if !tree.is_exec(recipe) {
        return Err(layout(format!("build.recipe {recipe:?} is not executable")));
    }
    let outs = &m.build.outputs;
    if outs.is_empty() || outs.len() > MAX_OUTPUTS {
        return Err(layout(format!("build.outputs must have 1..={MAX_OUTPUTS} entries")));
    }
    let uniq: BTreeSet<&str> = outs.iter().map(|s| s.as_str()).collect();
    if uniq.len() != outs.len() {
        return Err(layout("duplicate build.outputs"));
    }
    let nested = |a: &str, b: &str| b.len() > a.len() && b.starts_with(a) && b.as_bytes()[a.len()] == b'/';
    for a in outs {
        for b in outs {
            if nested(a, b) {
                return Err(layout(format!("build.outputs {a:?} and {b:?} are nested")));
            }
        }
        if tree.is_file(a) || tree.is_dir(a) {
            return Err(layout(format!("build output {a:?} already present in package")));
        }
        if crate::path::ancestors(a).any(|p| tree.is_file(p)) {
            return Err(layout(format!("build output {a:?} lies beneath a package file")));
        }
    }
    for (name, p) in [("prepare", &m.entry.prepare), ("prove", &m.entry.prove), ("verify", &m.entry.verify)] {
        if !outs.iter().any(|o| o == p || nested(o, p)) {
            return Err(layout(format!("entry.{name} {p:?} is not produced by build.outputs")));
        }
    }
    Ok(())
}
