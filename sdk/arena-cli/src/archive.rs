//! Package archive validation (`ARCHIVE_UNSAFE` / `MANIFEST_INVALID` rules from
//! `docs/CONTRACTS.md` §3).
//!
//! Thin adapter over the judge's authoritative implementation in
//! `runners/archive` (crate `arena-archive`), so `arena check-local` and the
//! server can never disagree.

use arena_types::{CandidateManifest, Digest};
use std::path::{Path, PathBuf};

/// Limits from CONTRACTS.md §3.
#[derive(Clone, Copy, Debug)]
pub struct ArchiveLimits {
    pub max_compressed_bytes: u64,
    pub max_expanded_bytes: u64,
    pub max_entries: u64,
    pub max_path_len: usize,
}

impl Default for ArchiveLimits {
    fn default() -> Self {
        ArchiveLimits {
            max_compressed_bytes: 256 << 20,
            max_expanded_bytes: 2 << 30,
            max_entries: 100_000,
            max_path_len: 255,
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ArchiveError {
    #[error("ARCHIVE_UNSAFE: {0}")]
    Unsafe(String),
    #[error("MANIFEST_INVALID: {0}")]
    Manifest(String),
}

/// Part of the seam API (mirrors what `runners/archive` reports).
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct ArchivedFile {
    pub path: String,
    pub exec: bool,
    pub size: u64,
    pub digest: Digest,
}

#[derive(Debug)]
pub struct ValidatedPackage {
    pub package_digest: Digest,
    pub compressed_bytes: u64,
    pub expanded_bytes: u64,
    pub files: Vec<ArchivedFile>,
    pub manifest: CandidateManifest,
}

/// Validate (and optionally extract) a package archive. This is the single
/// entry point used by the SDK. It delegates to the judge's own
/// implementation (`runners/archive`, crate `arena-archive`), so
/// `arena check-local` and the server apply exactly the same ingestion,
/// layout and manifest rules.
pub fn validate_package(
    bytes: &[u8],
    limits: &ArchiveLimits,
    extract_to: Option<&Path>,
) -> Result<ValidatedPackage, ArchiveError> {
    if limits.max_path_len != arena_archive::path::MAX_PATH_BYTES {
        return Err(ArchiveError::Unsafe(format!(
            "max_path_len is fixed at {} by the contract",
            arena_archive::path::MAX_PATH_BYTES
        )));
    }
    let l = arena_archive::Limits {
        max_compressed_bytes: limits.max_compressed_bytes,
        max_expanded_bytes: limits.max_expanded_bytes,
        max_entries: limits.max_entries,
        ..Default::default()
    };
    let tmp;
    let dest: PathBuf = match extract_to {
        Some(d) => {
            // `arena-archive` extracts into a fresh directory only.
            if d.exists() {
                let empty = std::fs::read_dir(d)
                    .map(|mut r| r.next().is_none())
                    .unwrap_or(false);
                if !empty {
                    return Err(ArchiveError::Unsafe(format!(
                        "{} is not empty",
                        d.display()
                    )));
                }
                std::fs::remove_dir(d).map_err(|e| ArchiveError::Unsafe(format!("io: {e}")))?;
            }
            d.to_path_buf()
        }
        None => {
            tmp = tempfile::tempdir().map_err(|e| ArchiveError::Unsafe(format!("io: {e}")))?;
            tmp.path().join("pkg")
        }
    };
    let x = arena_archive::ingest_bytes(bytes, &dest, &l).map_err(|e| match e {
        arena_archive::ArchiveError::Unsafe(m) => ArchiveError::Unsafe(m),
        arena_archive::ArchiveError::Io(e) => ArchiveError::Unsafe(format!("io: {e}")),
    })?;
    let manifest = arena_archive::validate_package(&x.root, &x.tree)
        .map_err(|e| ArchiveError::Manifest(e.to_string()))?;
    let files = x
        .tree
        .files
        .iter()
        .map(|(p, f)| ArchivedFile {
            path: p.clone(),
            exec: f.mode == arena_archive::FileMode::Exec,
            size: f.size,
            digest: f.digest.clone(),
        })
        .collect();
    Ok(ValidatedPackage {
        package_digest: Digest::of_bytes(bytes),
        compressed_bytes: x.compressed_bytes,
        expanded_bytes: x.tree.total_bytes(),
        files,
        manifest,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const MANIFEST: &str = r#"schema = "arena-candidate-v1"
name = "t"
agent = "a"
challenge = "chl_00"
backend_family = "x"
security_profile_request = "validity-classical-128"
hardware = { gpu = false, min_ram_gb = 1 }
[build]
recipe = "build-recipe/build.sh"
outputs = ["out/prepare", "out/prove", "out/verify"]
[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"
"#;

    fn raw_tar(entries: &[(&str, tar::EntryType, &[u8])]) -> Vec<u8> {
        let mut b = tar::Builder::new(Vec::new());
        for (p, t, d) in entries {
            let mut h = tar::Header::new_gnu();
            h.set_entry_type(*t);
            h.set_size(d.len() as u64);
            h.set_mode(0o644);
            // bypass the builder's own path sanitation to emit hostile names
            {
                let g = h.as_gnu_mut().unwrap();
                g.name[..p.len()].copy_from_slice(p.as_bytes());
            }
            if *t == tar::EntryType::Symlink {
                h.set_link_name("/etc/passwd").unwrap();
            }
            h.set_cksum();
            b.append(&h, *d).unwrap();
        }
        b.into_inner().unwrap()
    }

    #[test]
    fn accepts_good_and_zstd() {
        let mut b = tar::Builder::new(Vec::new());
        for (p, mode, d) in [
            ("candidate.toml", 0o644, MANIFEST.as_bytes()),
            ("README.md", 0o644, &b"x"[..]),
            ("source/lib.rs", 0o644, &b""[..]),
            ("dependency-locks/Cargo.lock", 0o644, &b""[..]),
            ("build-recipe/build.sh", 0o755, &b"#!/bin/sh\n"[..]),
        ] {
            let mut h = tar::Header::new_gnu();
            h.set_size(d.len() as u64);
            h.set_mode(mode);
            b.append_data(&mut h, p, d).unwrap();
        }
        let t = b.into_inner().unwrap();
        let v = validate_package(&t, &ArchiveLimits::default(), None).unwrap();
        assert_eq!(v.manifest.name, "t");
        assert!(v
            .files
            .iter()
            .any(|f| f.path == "build-recipe/build.sh" && f.exec));
        // Same rules as the judge: a package without README.md is refused.
        let bare = raw_tar(&[(
            "candidate.toml",
            tar::EntryType::Regular,
            MANIFEST.as_bytes(),
        )]);
        assert!(matches!(
            validate_package(&bare, &ArchiveLimits::default(), None),
            Err(ArchiveError::Manifest(_))
        ));
        let z = zstd::encode_all(t.as_slice(), 3).unwrap();
        validate_package(&z, &ArchiveLimits::default(), None).unwrap();
    }

    #[test]
    fn rejects_hostile() {
        let m = MANIFEST.as_bytes();
        let cases: Vec<Vec<(&str, tar::EntryType, &[u8])>> = vec![
            vec![
                ("../evil", tar::EntryType::Regular, b"x"),
                ("candidate.toml", tar::EntryType::Regular, m),
            ],
            vec![
                ("/abs", tar::EntryType::Regular, b"x"),
                ("candidate.toml", tar::EntryType::Regular, m),
            ],
            vec![
                ("link", tar::EntryType::Symlink, b""),
                ("candidate.toml", tar::EntryType::Regular, m),
            ],
            vec![
                ("hl", tar::EntryType::Link, b""),
                ("candidate.toml", tar::EntryType::Regular, m),
            ],
            vec![
                ("dev", tar::EntryType::Char, b""),
                ("candidate.toml", tar::EntryType::Regular, m),
            ],
            vec![
                ("candidate.toml", tar::EntryType::Regular, m),
                ("candidate.toml", tar::EntryType::Regular, m),
            ],
            vec![
                ("a/./b", tar::EntryType::Regular, b"x"),
                ("candidate.toml", tar::EntryType::Regular, m),
            ],
            vec![
                ("a", tar::EntryType::Regular, b"x"),
                ("a/b", tar::EntryType::Regular, b"x"),
                ("candidate.toml", tar::EntryType::Regular, m),
            ],
            vec![("x", tar::EntryType::Regular, b"x")],
        ];
        for c in cases {
            let t = raw_tar(&c);
            assert!(
                validate_package(&t, &ArchiveLimits::default(), None).is_err(),
                "{:?}",
                c[0].0
            );
        }
    }

    #[test]
    fn enforces_limits() {
        let t = raw_tar(&[
            (
                "candidate.toml",
                tar::EntryType::Regular,
                MANIFEST.as_bytes(),
            ),
            ("big", tar::EntryType::Regular, &[0u8; 4096]),
        ]);
        let l = ArchiveLimits {
            max_expanded_bytes: 2048,
            ..Default::default()
        };
        assert!(matches!(
            validate_package(&t, &l, None),
            Err(ArchiveError::Unsafe(_))
        ));
        let l = ArchiveLimits {
            max_entries: 1,
            ..Default::default()
        };
        assert!(validate_package(&t, &l, None).is_err());
        let l = ArchiveLimits {
            max_compressed_bytes: 100,
            ..Default::default()
        };
        assert!(validate_package(&t, &l, None).is_err());
    }

    #[test]
    fn manifest_errors_are_manifest_invalid() {
        let t = raw_tar(&[("candidate.toml", tar::EntryType::Regular, b"schema = 1")]);
        assert!(matches!(
            validate_package(&t, &ArchiveLimits::default(), None),
            Err(ArchiveError::Manifest(_))
        ));
    }
}
