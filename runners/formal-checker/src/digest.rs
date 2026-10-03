//! Digest helpers: file digests and the contract `TreeDigest` (CONTRACTS.md §1).

use arena_types::Digest;
use sha2::{Digest as _, Sha256};
use std::io::Read;
use std::path::Path;

pub fn sha256_file(p: &Path) -> std::io::Result<Digest> {
    let mut f = std::fs::File::open(p)?;
    let mut h = Sha256::new();
    let mut buf = vec![0u8; 1 << 16];
    loop {
        let n = f.read(&mut buf)?;
        if n == 0 {
            break;
        }
        h.update(&buf[..n]);
    }
    Ok(Digest::try_from(format!("sha256:{}", hex::encode(h.finalize()))).expect("valid"))
}

#[derive(Debug, thiserror::Error)]
pub enum TreeError {
    #[error("unsupported entry (symlink/device/other) at {0}")]
    Unsupported(String),
    #[error("non-utf8 or unsafe path {0}")]
    BadPath(String),
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
}

/// One entry of a tree listing.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct TreeEntry {
    pub path: String,
    pub exec: bool,
    pub digest: Digest,
}

/// List a directory tree: regular files only; symlinks/devices are an error.
pub fn list_tree(root: &Path) -> Result<Vec<TreeEntry>, TreeError> {
    use std::os::unix::fs::PermissionsExt;
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for ent in std::fs::read_dir(&dir)? {
            let ent = ent?;
            let p = ent.path();
            let ft = ent.file_type()?;
            let rel = p
                .strip_prefix(root)
                .ok()
                .and_then(|r| r.to_str())
                .ok_or_else(|| TreeError::BadPath(p.display().to_string()))?
                .to_string();
            if ft.is_symlink() {
                return Err(TreeError::Unsupported(rel));
            } else if ft.is_dir() {
                stack.push(p);
            } else if ft.is_file() {
                let mode = ent.metadata()?.permissions().mode();
                out.push(TreeEntry {
                    path: rel,
                    exec: mode & 0o111 != 0,
                    digest: sha256_file(&p)?,
                });
            } else {
                return Err(TreeError::Unsupported(rel));
            }
        }
    }
    out.sort();
    Ok(out)
}

/// `TreeDigest`: JCS array of `[path, "file"|"exec", digest]`, sorted by path.
pub fn tree_digest_of(entries: &[TreeEntry]) -> Digest {
    let arr: Vec<(String, &str, String)> = entries
        .iter()
        .map(|e| {
            (
                e.path.clone(),
                if e.exec { "exec" } else { "file" },
                e.digest.to_string(),
            )
        })
        .collect();
    arena_types::sha256_digest(&arr).expect("no floats")
}

pub fn tree_digest(root: &Path) -> Result<Digest, TreeError> {
    Ok(tree_digest_of(&list_tree(root)?))
}

pub fn json_digest<T: serde::Serialize>(v: &T) -> Digest {
    arena_types::sha256_digest(v).expect("no floats in checker objects")
}
