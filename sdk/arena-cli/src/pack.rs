//! Deterministic package archive (`arena pack`).
//!
//! Format: POSIX/GNU `tar`, regular-file entries only, sorted by path bytes,
//! `mtime = uid = gid = 0`, empty user/group names, mode `0755` if any exec
//! bit is set on the source file else `0644`. Directories are implied by file
//! paths. The same tree therefore always packs to the same bytes, and the
//! upload digest is a pure function of the tree.
//!
//! Excluded (never packed): any `.git/` or `.lake/` directory, Cargo `target/`
//! build dirs (top-level, or marked with `CACHEDIR.TAG`), and the
//! top-level `out/` directory (build outputs are produced by the judge).
//! Symlinks, sockets, devices and fifos make packing fail (`ARCHIVE_UNSAFE`).

use crate::exit::{CliError, CliResult};
use std::os::unix::fs::PermissionsExt;
use std::path::Path;

pub const EXCLUDED_ANY_DEPTH: &[&str] = &[".git", ".lake"];
/// `target` is excluded only when it is a Cargo build dir: at the package root
/// or containing `CACHEDIR.TAG`. Vendored crates (e.g. `cc`) ship source
/// directories named `target` that must be kept.
pub const CARGO_TARGET: &str = "target";
pub const EXCLUDED_TOP_LEVEL: &[&str] = &["out"];

/// One file to be packed.
#[derive(Debug, Clone)]
pub struct PackEntry {
    pub path: String,
    pub exec: bool,
    pub abs: std::path::PathBuf,
}

/// Collect the files of a candidate directory in canonical (sorted) order.
pub fn collect(root: &Path) -> CliResult<Vec<PackEntry>> {
    let mut out = Vec::new();
    walk(root, "", &mut out)?;
    out.sort_by(|a, b| a.path.as_bytes().cmp(b.path.as_bytes()));
    Ok(out)
}

fn walk(dir: &Path, rel: &str, out: &mut Vec<PackEntry>) -> CliResult<()> {
    let rd = std::fs::read_dir(dir)
        .map_err(|e| CliError::local(format!("cannot read {}: {e}", dir.display())))?;
    for ent in rd {
        let ent = ent?;
        let name = ent.file_name();
        let name = name.to_str().ok_or_else(|| {
            CliError::local(format!(
                "ARCHIVE_UNSAFE: non-UTF-8 file name in {}",
                dir.display()
            ))
        })?;
        let relp = if rel.is_empty() {
            name.to_string()
        } else {
            format!("{rel}/{name}")
        };
        let ft = ent.file_type()?;
        if ft.is_dir() {
            if EXCLUDED_ANY_DEPTH.contains(&name)
                || (rel.is_empty() && EXCLUDED_TOP_LEVEL.contains(&name))
                || (name == CARGO_TARGET
                    && (rel.is_empty() || ent.path().join("CACHEDIR.TAG").exists()))
            {
                continue;
            }
            walk(&ent.path(), &relp, out)?;
        } else if ft.is_file() {
            let md = ent.metadata()?;
            out.push(PackEntry {
                path: relp,
                exec: md.permissions().mode() & 0o111 != 0,
                abs: ent.path(),
            });
        } else if ft.is_symlink() {
            return Err(CliError::local(format!(
                "ARCHIVE_UNSAFE: symlink not allowed: {relp}"
            )));
        } else {
            return Err(CliError::local(format!(
                "ARCHIVE_UNSAFE: special file not allowed: {relp}"
            )));
        }
    }
    Ok(())
}

/// Pack `root` into deterministic tar bytes.
pub fn pack_dir(root: &Path) -> CliResult<Vec<u8>> {
    let entries = collect(root)?;
    let mut b = tar::Builder::new(Vec::new());
    b.mode(tar::HeaderMode::Deterministic);
    for e in &entries {
        let data = std::fs::read(&e.abs)?;
        let mut h = tar::Header::new_gnu();
        h.set_entry_type(tar::EntryType::Regular);
        h.set_size(data.len() as u64);
        h.set_mode(if e.exec { 0o755 } else { 0o644 });
        h.set_mtime(0);
        h.set_uid(0);
        h.set_gid(0);
        h.set_username("")
            .map_err(|e| CliError::internal(e.to_string()))?;
        h.set_groupname("")
            .map_err(|e| CliError::internal(e.to_string()))?;
        b.append_data(&mut h, &e.path, data.as_slice())
            .map_err(|err| CliError::local(format!("cannot pack {}: {err}", e.path)))?;
    }
    b.into_inner().map_err(CliError::from)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn mk(dir: &Path) {
        fs::create_dir_all(dir.join("source/src")).unwrap();
        fs::create_dir_all(dir.join("out")).unwrap();
        fs::create_dir_all(dir.join("source/target")).unwrap();
        fs::write(dir.join("candidate.toml"), "x").unwrap();
        fs::write(dir.join("source/src/b.rs"), "b").unwrap();
        fs::write(dir.join("source/src/a.rs"), "a").unwrap();
        fs::write(dir.join("out/prove"), "bin").unwrap();
        fs::write(dir.join("source/target/junk"), "junk").unwrap();
        // Cargo marks build dirs with CACHEDIR.TAG; only those are dropped below the root.
        fs::write(
            dir.join("source/target/CACHEDIR.TAG"),
            "Signature: 8a477f597d28d172789f06886806bc55",
        )
        .unwrap();
        // A vendored source dir named `target` (e.g. the `cc` crate) must be kept.
        fs::create_dir_all(dir.join("source/vendor/cc/src/target")).unwrap();
        fs::write(dir.join("source/vendor/cc/src/target/mod.rs"), "//").unwrap();
        fs::write(dir.join("run.sh"), "#!/bin/sh").unwrap();
        fs::set_permissions(dir.join("run.sh"), fs::Permissions::from_mode(0o700)).unwrap();
    }

    #[test]
    fn deterministic_and_sorted() {
        let t1 = tempfile::tempdir().unwrap();
        let t2 = tempfile::tempdir().unwrap();
        mk(t1.path());
        mk(t2.path());
        // Different mtimes / creation order must not matter.
        fs::write(t2.path().join("source/src/a.rs"), "a").unwrap();
        let a = pack_dir(t1.path()).unwrap();
        let b = pack_dir(t2.path()).unwrap();
        assert_eq!(a, b);
        let mut ar = tar::Archive::new(a.as_slice());
        let names: Vec<(String, u32, u64)> = ar
            .entries()
            .unwrap()
            .map(|e| {
                let e = e.unwrap();
                let h = e.header();
                (
                    e.path().unwrap().to_str().unwrap().to_string(),
                    h.mode().unwrap(),
                    h.mtime().unwrap(),
                )
            })
            .collect();
        assert_eq!(
            names,
            vec![
                ("candidate.toml".into(), 0o644, 0),
                ("run.sh".into(), 0o755, 0),
                ("source/src/a.rs".into(), 0o644, 0),
                ("source/src/b.rs".into(), 0o644, 0),
                ("source/vendor/cc/src/target/mod.rs".into(), 0o644, 0),
            ]
        );
    }

    #[test]
    fn rejects_symlink() {
        let t = tempfile::tempdir().unwrap();
        fs::write(t.path().join("a"), "a").unwrap();
        std::os::unix::fs::symlink("a", t.path().join("b")).unwrap();
        assert!(pack_dir(t.path()).is_err());
    }

    #[test]
    fn long_paths_roundtrip() {
        let t = tempfile::tempdir().unwrap();
        let deep = "d".repeat(60) + "/" + &"e".repeat(60);
        fs::create_dir_all(t.path().join(&deep)).unwrap();
        fs::write(t.path().join(&deep).join("f.txt"), "x").unwrap();
        let a = pack_dir(t.path()).unwrap();
        let mut ar = tar::Archive::new(a.as_slice());
        let p: Vec<String> = ar
            .entries()
            .unwrap()
            .map(|e| e.unwrap().path().unwrap().to_str().unwrap().to_string())
            .collect();
        assert_eq!(p, vec![format!("{deep}/f.txt")]);
    }
}
