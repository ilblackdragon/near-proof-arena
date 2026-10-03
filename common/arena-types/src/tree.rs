//! `TreeDigest` (CONTRACTS §1): the single shared implementation.
//!
//! Digest of the JCS array of `[relative_path, "file"|"exec", "sha256:.."]`
//! entries sorted by path bytes. Symlinks and special files are rejected;
//! paths use `/` separators and must be UTF-8.

use crate::{canonical_json, Digest};
use std::path::Path;

#[derive(Debug, thiserror::Error)]
pub enum TreeError {
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
    #[error("unsupported entry in tree: {0}")]
    Unsupported(String),
    #[error("canonical: {0}")]
    Canonical(#[from] crate::canonical::CanonicalError),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeEntry {
    pub path: String,
    pub exec: bool,
    pub digest: Digest,
}

/// Digest of already-collected entries (order-independent; sorted here).
pub fn tree_digest_entries(mut entries: Vec<TreeEntry>) -> Result<Digest, TreeError> {
    entries.sort_by(|a, b| a.path.as_bytes().cmp(b.path.as_bytes()));
    let arr: Vec<serde_json::Value> = entries
        .into_iter()
        .map(|e| {
            serde_json::json!([
                e.path,
                if e.exec { "exec" } else { "file" },
                e.digest.as_str()
            ])
        })
        .collect();
    Ok(Digest::of_bytes(&canonical_json(&arr)?))
}

/// Walk `root` (not following symlinks) and compute its TreeDigest.
pub fn tree_digest(root: &Path) -> Result<Digest, TreeError> {
    fn walk(root: &Path, dir: &Path, out: &mut Vec<TreeEntry>) -> Result<(), TreeError> {
        for e in std::fs::read_dir(dir)? {
            let p = e?.path();
            let ft = std::fs::symlink_metadata(&p)?.file_type();
            if ft.is_dir() {
                walk(root, &p, out)?;
            } else if ft.is_file() {
                let rel = p
                    .strip_prefix(root)
                    .ok()
                    .and_then(|r| r.to_str())
                    .ok_or_else(|| TreeError::Unsupported(p.display().to_string()))?
                    .replace(std::path::MAIN_SEPARATOR, "/");
                #[cfg(unix)]
                let exec = {
                    use std::os::unix::fs::PermissionsExt;
                    std::fs::metadata(&p)?.permissions().mode() & 0o111 != 0
                };
                #[cfg(not(unix))]
                let exec = false;
                out.push(TreeEntry {
                    path: rel,
                    exec,
                    digest: Digest::of_bytes(&std::fs::read(&p)?),
                });
            } else {
                return Err(TreeError::Unsupported(p.display().to_string()));
            }
        }
        Ok(())
    }
    let mut entries = Vec::new();
    walk(root, root, &mut entries)?;
    tree_digest_entries(entries)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn stable_vector() {
        let d = tree_digest_entries(vec![
            TreeEntry {
                path: "b".into(),
                exec: true,
                digest: Digest::of_bytes(b"x"),
            },
            TreeEntry {
                path: "a/c".into(),
                exec: false,
                digest: Digest::of_bytes(b""),
            },
        ])
        .unwrap();
        // Order-independence and format pin (JCS of the sorted array).
        let expect = Digest::of_bytes(
            format!(
                "[[\"a/c\",\"file\",\"{}\"],[\"b\",\"exec\",\"{}\"]]",
                Digest::of_bytes(b""),
                Digest::of_bytes(b"x")
            )
            .as_bytes(),
        );
        assert_eq!(d, expect);
    }
}
