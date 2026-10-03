//! Package archive validation (`ARCHIVE_UNSAFE` / `MANIFEST_INVALID` rules from
//! `docs/CONTRACTS.md` §3).
//!
//! SEAM: the judge's authoritative implementation lives in `runners/archive`
//! (runners-core lane). Until that crate is on `main` the SDK carries this
//! re-implementation of the same rules. Everything the CLI needs goes through
//! [`validate_package`]; when `runners/archive` lands, replace the body of
//! that function with a call into the shared crate and keep this signature,
//! so `arena check-local` and the server can never disagree.

use arena_types::{CandidateManifest, Digest};
use std::collections::BTreeSet;
use std::io::Read;
use std::path::Path;

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

const ZSTD_MAGIC: [u8; 4] = [0x28, 0xb5, 0x2f, 0xfd];

fn safe_path(p: &str, max_len: usize) -> Result<(), String> {
    if p.is_empty() || p.len() > max_len {
        return Err(format!("path length out of range: {p:?}"));
    }
    if p.starts_with('/') {
        return Err(format!("absolute path: {p:?}"));
    }
    if p.bytes()
        .any(|b| b == 0 || b == b'\\' || b < 0x20 || b == 0x7f)
    {
        return Err(format!("control/backslash character in path: {p:?}"));
    }
    if p.split('/').any(|c| c.is_empty() || c == "." || c == "..") {
        return Err(format!("non-normal path component: {p:?}"));
    }
    Ok(())
}

/// Validate (and optionally extract) a package archive. This is the single
/// entry point used by the SDK (see module docs for the seam).
pub fn validate_package(
    bytes: &[u8],
    limits: &ArchiveLimits,
    extract_to: Option<&Path>,
) -> Result<ValidatedPackage, ArchiveError> {
    let un = |s: String| ArchiveError::Unsafe(s);
    if bytes.len() as u64 > limits.max_compressed_bytes {
        return Err(un(format!(
            "archive is {} bytes > {} limit",
            bytes.len(),
            limits.max_compressed_bytes
        )));
    }
    let package_digest = Digest::of_bytes(bytes);
    let reader: Box<dyn Read + '_> = if bytes.starts_with(&ZSTD_MAGIC) {
        Box::new(zstd::stream::read::Decoder::new(bytes).map_err(|e| un(format!("zstd: {e}")))?)
    } else {
        Box::new(bytes)
    };
    // Hard cap on decompressed stream (tar overhead included) as a bomb guard.
    let cap = limits.max_expanded_bytes + (limits.max_entries + 2) * 1024 + 1;
    let mut ar = tar::Archive::new(reader.take(cap));
    let mut seen = BTreeSet::new();
    let mut files = Vec::new();
    let mut expanded: u64 = 0;
    let mut count: u64 = 0;
    let mut manifest_src: Option<String> = None;
    for ent in ar.entries().map_err(|e| un(format!("tar: {e}")))? {
        let mut ent = ent.map_err(|e| un(format!("tar: {e}")))?;
        count += 1;
        if count > limits.max_entries {
            return Err(un(format!("more than {} entries", limits.max_entries)));
        }
        let raw = ent.path_bytes().into_owned();
        let path = String::from_utf8(raw).map_err(|_| un("non-UTF-8 path".into()))?;
        let et = ent.header().entry_type();
        let is_dir = et.is_dir();
        let norm = if is_dir {
            path.trim_end_matches('/').to_string()
        } else {
            path.clone()
        };
        safe_path(&norm, limits.max_path_len).map_err(un)?;
        if !(et.is_file() || is_dir) {
            return Err(un(format!("entry type {:?} not allowed: {norm}", et)));
        }
        if !seen.insert(norm.clone()) {
            return Err(un(format!("duplicate entry: {norm}")));
        }
        if is_dir {
            if let Some(root) = extract_to {
                std::fs::create_dir_all(root.join(&norm)).map_err(|e| un(e.to_string()))?;
            }
            continue;
        }
        let size = ent.header().size().map_err(|e| un(e.to_string()))?;
        expanded = expanded.saturating_add(size);
        if expanded > limits.max_expanded_bytes {
            return Err(un(format!(
                "expanded size exceeds {} bytes",
                limits.max_expanded_bytes
            )));
        }
        let mode = ent.header().mode().map_err(|e| un(e.to_string()))?;
        let mut data = Vec::with_capacity(size.min(1 << 24) as usize);
        (&mut ent)
            .take(size)
            .read_to_end(&mut data)
            .map_err(|e| un(format!("tar: {e}")))?;
        if data.len() as u64 != size {
            return Err(un(format!("truncated entry: {norm}")));
        }
        if norm == "candidate.toml" {
            manifest_src = Some(
                String::from_utf8(data.clone())
                    .map_err(|_| ArchiveError::Manifest("candidate.toml is not UTF-8".into()))?,
            );
        }
        let exec = mode & 0o111 != 0;
        if let Some(root) = extract_to {
            let dst = root.join(&norm);
            if let Some(parent) = dst.parent() {
                std::fs::create_dir_all(parent).map_err(|e| un(e.to_string()))?;
            }
            std::fs::write(&dst, &data).map_err(|e| un(e.to_string()))?;
            use std::os::unix::fs::PermissionsExt;
            let m = if exec { 0o755 } else { 0o644 };
            std::fs::set_permissions(&dst, std::fs::Permissions::from_mode(m))
                .map_err(|e| un(e.to_string()))?;
        }
        files.push(ArchivedFile {
            path: norm,
            exec,
            size,
            digest: Digest::of_bytes(&data),
        });
    }
    // A directory entry and a file with the same name prefix would collide.
    let file_set: BTreeSet<&str> = files.iter().map(|f| f.path.as_str()).collect();
    for f in &files {
        let mut p = f.path.as_str();
        while let Some(i) = p.rfind('/') {
            p = &p[..i];
            if file_set.contains(p) {
                return Err(un(format!("path {p} is both a file and a directory")));
            }
        }
    }
    let src = manifest_src
        .ok_or_else(|| ArchiveError::Manifest("candidate.toml missing at archive root".into()))?;
    let manifest =
        CandidateManifest::parse(&src).map_err(|e| ArchiveError::Manifest(e.to_string()))?;
    Ok(ValidatedPackage {
        package_digest,
        compressed_bytes: bytes.len() as u64,
        expanded_bytes: expanded,
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
        let t = raw_tar(&[(
            "candidate.toml",
            tar::EntryType::Regular,
            MANIFEST.as_bytes(),
        )]);
        let v = validate_package(&t, &ArchiveLimits::default(), None).unwrap();
        assert_eq!(v.manifest.name, "t");
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
