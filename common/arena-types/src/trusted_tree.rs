//! Frozen trusted trees (docs/TCB.md §"Frozen trusted trees").
//!
//! Every challenge pins `semantic_scope.formal_spec.tree_digest`: the
//! TreeDigest of the git-tracked files under `formal-core/` and `spec/lean/`,
//! with repository-relative paths (`spec/tools/tree_digest.py spec/lean
//! formal-core`). The judge never builds the trusted reference (ArenaCore,
//! NearSpec, the Expected templates) from a working checkout: it builds from
//! a *frozen trusted tree*, a content-addressed snapshot of exactly those two
//! roots, stored as `<store>/<hex>/{formal-core,spec/lean}/…` and named by
//! the digest it must have.
//!
//! The store is judge-owned and published with `arena-admin freeze-trusted`.
//! Nothing trusts the store's naming: [`check`] (registration) and
//! [`materialize`] (FORMAL_CHECK) recompute the digest from the files
//! themselves, and `materialize` does it on the job-private copy that is
//! actually built, so a later change to the store cannot reach a build.

use crate::tree::{tree_digest_entries, tree_entries, TreeEntry, TreeError};
use crate::Digest;
use std::path::{Path, PathBuf};

/// The repository roots a challenge's `formal_spec.tree_digest` covers.
pub const TRUSTED_ROOTS: [&str; 2] = ["formal-core", "spec/lean"];

#[derive(Debug, thiserror::Error)]
pub enum TrustedTreeError {
    #[error("the all-zero placeholder digest names no trusted tree")]
    Placeholder,
    #[error("frozen trusted tree {digest} is not in the store ({path} missing; publish it with `arena-admin freeze-trusted`)")]
    Missing { digest: Digest, path: PathBuf },
    #[error("trusted tree at {path} has TreeDigest {got}, not the pinned {want} (tampered or wrong tree)")]
    Mismatch {
        path: PathBuf,
        want: Digest,
        got: Digest,
    },
    #[error("trusted tree at {path}: root {root}/ is missing or not a directory")]
    MissingRoot { path: PathBuf, root: &'static str },
    #[error("trusted tree: {0}")]
    Tree(#[from] TreeError),
    #[error("trusted tree io: {0}")]
    Io(#[from] std::io::Error),
}

fn root_entries(root: &Path) -> Result<Vec<TreeEntry>, TrustedTreeError> {
    let mut all = Vec::new();
    for r in TRUSTED_ROOTS {
        let dir = root.join(r);
        let md = std::fs::symlink_metadata(&dir).ok();
        if !md.is_some_and(|m| m.is_dir()) {
            return Err(TrustedTreeError::MissingRoot {
                path: root.to_path_buf(),
                root: r,
            });
        }
        for mut e in tree_entries(&dir)? {
            e.path = format!("{r}/{}", e.path);
            all.push(e);
        }
    }
    Ok(all)
}

/// TreeDigest of `<root>/formal-core` + `<root>/spec/lean`, paths relative to
/// `root` (equals `tree_digest.py spec/lean formal-core` on a clean checkout).
/// Anything else under `root` is ignored.
pub fn digest_of(root: &Path) -> Result<Digest, TrustedTreeError> {
    Ok(tree_digest_entries(root_entries(root)?)?)
}

/// `<store>/<hex>`: where the frozen tree with this digest lives.
pub fn entry_dir(store: &Path, digest: &Digest) -> PathBuf {
    store.join(digest.hex())
}

fn is_placeholder(d: &Digest) -> bool {
    d.hex().bytes().all(|b| b == b'0')
}

/// The pinned tree is in `store` and its files hash to `digest` (registration
/// gate). Returns the entry directory.
pub fn check(store: &Path, digest: &Digest) -> Result<PathBuf, TrustedTreeError> {
    if is_placeholder(digest) {
        return Err(TrustedTreeError::Placeholder);
    }
    let dir = entry_dir(store, digest);
    if !dir.is_dir() {
        return Err(TrustedTreeError::Missing {
            digest: digest.clone(),
            path: dir,
        });
    }
    let got = digest_of(&dir)?;
    if &got != digest {
        return Err(TrustedTreeError::Mismatch {
            path: dir,
            want: digest.clone(),
            got,
        });
    }
    Ok(dir)
}

/// Copy the frozen tree `digest` from `store` into the fresh directory
/// `dest` (which must not exist) and re-verify the digest **on the copy**:
/// what is built afterwards is exactly what was hashed. On any error `dest`
/// is removed.
pub fn materialize(store: &Path, digest: &Digest, dest: &Path) -> Result<(), TrustedTreeError> {
    let res = (|| {
        if is_placeholder(digest) {
            return Err(TrustedTreeError::Placeholder);
        }
        let src = entry_dir(store, digest);
        if !src.is_dir() {
            return Err(TrustedTreeError::Missing {
                digest: digest.clone(),
                path: src,
            });
        }
        std::fs::create_dir(dest)?;
        for e in root_entries(&src)? {
            let to = dest.join(&e.path);
            std::fs::create_dir_all(to.parent().expect("relative path has a parent"))?;
            std::fs::copy(src.join(&e.path), &to)?;
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let mode = if e.exec { 0o755 } else { 0o644 };
                std::fs::set_permissions(&to, std::fs::Permissions::from_mode(mode))?;
            }
        }
        let got = digest_of(dest)?;
        if &got != digest {
            return Err(TrustedTreeError::Mismatch {
                path: src,
                want: digest.clone(),
                got,
            });
        }
        Ok(())
    })();
    if res.is_err() {
        let _ = std::fs::remove_dir_all(dest);
    }
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmpdir(tag: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!(
            "arena-trusted-{tag}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    fn write(root: &Path, rel: &str, body: &str) {
        let p = root.join(rel);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, body).unwrap();
    }

    /// A store with one correct entry; returns (store, digest).
    fn store_with_tree(tag: &str) -> (PathBuf, Digest) {
        let base = tmpdir(tag);
        let src = base.join("src");
        write(&src, "formal-core/ArenaCore.lean", "-- core\n");
        write(&src, "spec/lean/NearSpec.lean", "-- spec\n");
        write(&src, "spec/lean/judge/Expected.lean.template", "x\n");
        let d = digest_of(&src).unwrap();
        let store = base.join("store");
        std::fs::create_dir_all(&store).unwrap();
        std::fs::rename(&src, entry_dir(&store, &d)).unwrap();
        (store, d)
    }

    #[test]
    fn digest_matches_repo_relative_tree_digest() {
        let base = tmpdir("vec");
        write(&base, "formal-core/A.lean", "a");
        write(&base, "spec/lean/B.lean", "b");
        write(&base, "other/ignored", "z");
        let want = tree_digest_entries(vec![
            TreeEntry {
                path: "formal-core/A.lean".into(),
                exec: false,
                digest: Digest::of_bytes(b"a"),
            },
            TreeEntry {
                path: "spec/lean/B.lean".into(),
                exec: false,
                digest: Digest::of_bytes(b"b"),
            },
        ])
        .unwrap();
        assert_eq!(digest_of(&base).unwrap(), want);
    }

    #[test]
    fn correct_tree_materializes() {
        let (store, d) = store_with_tree("ok");
        assert!(check(&store, &d).is_ok());
        let dest = store.parent().unwrap().join("job");
        materialize(&store, &d, &dest).unwrap();
        assert_eq!(digest_of(&dest).unwrap(), d);
        assert!(dest
            .join("spec/lean/judge/Expected.lean.template")
            .is_file());
    }

    #[test]
    fn tampered_tree_is_refused() {
        let (store, d) = store_with_tree("tamper");
        write(
            &entry_dir(&store, &d),
            "formal-core/ArenaCore.lean",
            "-- core\naxiom bad : False\n",
        );
        assert!(matches!(
            check(&store, &d),
            Err(TrustedTreeError::Mismatch { .. })
        ));
        let dest = store.parent().unwrap().join("job");
        assert!(matches!(
            materialize(&store, &d, &dest),
            Err(TrustedTreeError::Mismatch { .. })
        ));
        assert!(!dest.exists(), "a refused tree leaves nothing to build");
        // An added file is a different tree too.
        let (store, d) = store_with_tree("tamper-add");
        write(&entry_dir(&store, &d), "spec/lean/Extra.lean", "");
        assert!(check(&store, &d).is_err());
    }

    #[test]
    fn wrong_or_missing_digest_is_refused() {
        let (store, d) = store_with_tree("wrong");
        // A correct tree stored under another digest's name.
        let other = Digest::of_bytes(b"other");
        std::fs::rename(entry_dir(&store, &d), entry_dir(&store, &other)).unwrap();
        assert!(matches!(
            check(&store, &other),
            Err(TrustedTreeError::Mismatch { .. })
        ));
        assert!(matches!(
            check(&store, &d),
            Err(TrustedTreeError::Missing { .. })
        ));
        let zero: Digest = format!("sha256:{}", "0".repeat(64)).try_into().unwrap();
        assert!(matches!(
            check(&store, &zero),
            Err(TrustedTreeError::Placeholder)
        ));
    }
}
