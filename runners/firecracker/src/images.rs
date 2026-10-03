//! Disk images: read-only bundle images (content-addressed cache), fresh
//! scratch filesystems and raw control/output devices.
//!
//! Bundle images are built with `mkfs.ext4 -d` from a *staging copy* of the
//! source tree: the copy is what gets hashed and what gets imaged, so a
//! concurrent modification of the source cannot make the digest and the
//! image disagree. The staging copy normalizes permissions (0644/0755,
//! dirs 0755) because only file-vs-exec is meaningful (CONTRACTS §1).
//! Symlinks, hardlinks, devices, fifos and sockets are rejected.

use arena_sandbox::InfraError;
use arena_fc_proto::validate_rel_path;
use arena_types::{canonical_json, Digest};
use sha2::{Digest as _, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;

/// Limits applied to every read-only tree (CONTRACTS §3 archive limits).
#[derive(Clone, Debug)]
pub struct TreeLimits {
    pub max_entries: u64,
    pub max_bytes: u64,
}

impl Default for TreeLimits {
    fn default() -> Self {
        TreeLimits {
            max_entries: 100_000,
            max_bytes: 8 << 30,
        }
    }
}

#[derive(Debug, Clone)]
pub struct StagedTree {
    pub dir: PathBuf,
    /// `TreeDigest` of the staged content (CONTRACTS §1).
    pub digest: Digest,
    pub files: u64,
    pub dirs: u64,
    pub bytes: u64,
    pub blocks: u64,
}

fn spec_err(s: impl Into<String>) -> InfraError {
    InfraError::InvalidSpec(s.into())
}

/// Copy `src` (a directory) into a fresh `dst`, validating and hashing.
pub fn stage_tree(src: &Path, dst: &Path, limits: &TreeLimits) -> Result<StagedTree, InfraError> {
    let md = fs::symlink_metadata(src).map_err(|e| spec_err(format!("{}: {e}", src.display())))?;
    if !md.is_dir() {
        return Err(spec_err(format!("{} is not a directory", src.display())));
    }
    fs::create_dir(dst)?;
    let mut entries: Vec<(String, &'static str, String)> = Vec::new();
    let mut st = StagedTree {
        dir: dst.to_path_buf(),
        digest: Digest::of_bytes(b""),
        files: 0,
        dirs: 0,
        bytes: 0,
        blocks: 0,
    };
    copy_dir(src, dst, "", limits, &mut st, &mut entries, 0)?;
    entries.sort();
    let list: Vec<serde_json::Value> = entries
        .into_iter()
        .map(|(p, m, h)| serde_json::json!([p, m, h]))
        .collect();
    let jcs = canonical_json(&list).map_err(|e| InfraError::Backend(e.to_string()))?;
    st.digest = Digest::of_bytes(&jcs);
    Ok(st)
}

#[allow(clippy::too_many_arguments)]
fn copy_dir(
    src: &Path,
    dst: &Path,
    rel: &str,
    limits: &TreeLimits,
    st: &mut StagedTree,
    entries: &mut Vec<(String, &'static str, String)>,
    depth: u32,
) -> Result<(), InfraError> {
    if depth > 64 {
        return Err(spec_err(format!("{rel}: tree too deep")));
    }
    let mut names: Vec<_> = fs::read_dir(src)?.collect::<Result<Vec<_>, _>>()?;
    names.sort_by_key(|e| e.file_name());
    for e in names {
        let name = e.file_name();
        let name = name
            .to_str()
            .ok_or_else(|| spec_err(format!("{rel}: non-utf8 file name")))?;
        let relp = if rel.is_empty() {
            name.to_string()
        } else {
            format!("{rel}/{name}")
        };
        validate_rel_path(&relp).map_err(|m| spec_err(format!("{relp:?}: {m}")))?;
        if st.files + st.dirs >= limits.max_entries {
            return Err(spec_err("too many entries"));
        }
        let md = fs::symlink_metadata(e.path())?;
        let ft = md.file_type();
        let to = dst.join(name);
        if ft.is_dir() {
            fs::create_dir(&to)?;
            fs::set_permissions(&to, fs::Permissions::from_mode(0o755))?;
            st.dirs += 1;
            copy_dir(&e.path(), &to, &relp, limits, st, entries, depth + 1)?;
        } else if ft.is_file() {
            if md.nlink() > 1 {
                return Err(spec_err(format!("{relp:?}: hardlinks are not allowed")));
            }
            let exec = md.mode() & 0o111 != 0;
            let mut inp = OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_NOFOLLOW)
                .open(e.path())?;
            let mut out = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(if exec { 0o755 } else { 0o644 })
                .open(&to)?;
            let mut h = Sha256::new();
            let mut buf = vec![0u8; 1 << 20];
            let mut n_total = 0u64;
            loop {
                let n = inp.read(&mut buf)?;
                if n == 0 {
                    break;
                }
                h.update(&buf[..n]);
                out.write_all(&buf[..n])?;
                n_total += n as u64;
                if st.bytes + n_total > limits.max_bytes {
                    return Err(spec_err("tree exceeds byte limit"));
                }
            }
            st.bytes += n_total;
            st.blocks += n_total.div_ceil(4096);
            st.files += 1;
            entries.push((
                relp,
                if exec { "exec" } else { "file" },
                format!("sha256:{}", hex::encode(h.finalize())),
            ));
        } else {
            return Err(spec_err(format!(
                "{relp:?}: symlinks/devices/fifos/sockets are not allowed"
            )));
        }
    }
    Ok(())
}

fn run_mkfs(args: &[&str], image: &Path) -> Result<(), InfraError> {
    let out = Command::new("mkfs.ext4")
        .args(args)
        .arg(image)
        .env_clear()
        .env("PATH", "/usr/sbin:/sbin:/usr/bin:/bin")
        .output()
        .map_err(|e| InfraError::Unavailable(format!("mkfs.ext4: {e}")))?;
    if !out.status.success() {
        return Err(InfraError::Backend(format!(
            "mkfs.ext4 failed: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        )));
    }
    Ok(())
}

fn create_sparse(path: &Path, bytes: u64) -> Result<File, InfraError> {
    let f = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)?;
    f.set_len(bytes)?;
    Ok(f)
}

/// Build a read-only ext4 image (no journal) from a staged tree.
pub fn build_ro_image(st: &StagedTree, image: &Path) -> Result<(), InfraError> {
    let inodes = st.files + st.dirs + 64;
    // data blocks + per-inode/dir overhead + fixed metadata, with headroom
    let mut size = (st.blocks + st.dirs + inodes / 16 + 2048) * 4096;
    size = size + size / 8 + (4 << 20);
    let mut last = None;
    for _ in 0..4 {
        let _ = fs::remove_file(image);
        create_sparse(image, size.div_ceil(4096) * 4096)?;
        let n = inodes.to_string();
        let r = run_mkfs(
            &[
                "-q",
                "-F",
                "-t",
                "ext4",
                "-b",
                "4096",
                "-I",
                "256",
                "-m",
                "0",
                "-N",
                &n,
                "-L",
                "arena-ro",
                "-O",
                "^has_journal,^resize_inode",
                "-E",
                "root_owner=0:0,lazy_itable_init=0,nodiscard",
                "-d",
                st.dir
                    .to_str()
                    .ok_or_else(|| spec_err("non-utf8 staging path"))?,
            ],
            image,
        );
        match r {
            Ok(()) => {
                fs::set_permissions(image, fs::Permissions::from_mode(0o444))?;
                return Ok(());
            }
            Err(e) => {
                last = Some(e);
                size *= 2;
            }
        }
    }
    Err(last.unwrap())
}

/// Fresh empty ext4 scratch filesystem owned by the guest candidate uid.
pub fn build_scratch_image(image: &Path, mb: u64) -> Result<(), InfraError> {
    create_sparse(image, mb << 20)?;
    let owner = format!(
        "root_owner={}:{},lazy_itable_init=1,lazy_journal_init=1,nodiscard",
        arena_fc_proto::CANDIDATE_UID,
        arena_fc_proto::CANDIDATE_GID
    );
    run_mkfs(
        &[
            "-q",
            "-F",
            "-t",
            "ext4",
            "-b",
            "4096",
            "-m",
            "0",
            "-L",
            "arena-scratch",
            "-O",
            "^has_journal",
            "-E",
            &owner,
        ],
        image,
    )
}

/// Raw device file holding `content` padded to 4 KiB.
pub fn build_raw_image(image: &Path, content: &[u8], min_size: u64) -> Result<(), InfraError> {
    let mut f = create_sparse(
        image,
        min_size.max(content.len() as u64).div_ceil(4096) * 4096,
    )?;
    f.write_all(content)?;
    f.sync_data().ok();
    Ok(())
}

/// sha256 of a file's raw bytes.
pub fn file_digest(path: &Path) -> io::Result<Digest> {
    let mut f = File::open(path)?;
    let mut h = Sha256::new();
    let mut buf = vec![0u8; 1 << 20];
    loop {
        let n = f.read(&mut buf)?;
        if n == 0 {
            break;
        }
        h.update(&buf[..n]);
    }
    Ok(Digest::try_from(format!("sha256:{}", hex::encode(h.finalize()))).expect("valid digest"))
}

/// Hardlink `src` to `dst`, falling back to a copy across filesystems.
pub fn link_or_copy(src: &Path, dst: &Path) -> io::Result<()> {
    match fs::hard_link(src, dst) {
        Ok(()) => Ok(()),
        Err(e)
            if e.raw_os_error() == Some(libc::EXDEV)
                || e.kind() == io::ErrorKind::PermissionDenied =>
        {
            fs::copy(src, dst)?;
            fs::set_permissions(dst, fs::Permissions::from_mode(0o444))
        }
        Err(e) => Err(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stage_rejects_symlinks_and_digests_deterministically() {
        let t = tempfile::tempdir().unwrap();
        let src = t.path().join("src");
        fs::create_dir_all(src.join("d")).unwrap();
        fs::write(src.join("a.txt"), b"hello").unwrap();
        fs::write(src.join("d/run"), b"#!/bin/sh\n").unwrap();
        fs::set_permissions(src.join("d/run"), fs::Permissions::from_mode(0o700)).unwrap();
        let a = stage_tree(&src, &t.path().join("s1"), &TreeLimits::default()).unwrap();
        let b = stage_tree(&src, &t.path().join("s2"), &TreeLimits::default()).unwrap();
        assert_eq!(a.digest, b.digest);
        assert_eq!((a.files, a.dirs, a.bytes), (2, 1, 15));
        assert_eq!(
            fs::metadata(t.path().join("s1/d/run")).unwrap().mode() & 0o777,
            0o755
        );
        std::os::unix::fs::symlink("/etc/passwd", src.join("evil")).unwrap();
        assert!(stage_tree(&src, &t.path().join("s3"), &TreeLimits::default()).is_err());
        fs::remove_file(src.join("evil")).unwrap();
        fs::hard_link(src.join("a.txt"), src.join("b.txt")).unwrap();
        assert!(stage_tree(&src, &t.path().join("s4"), &TreeLimits::default()).is_err());
    }

    #[test]
    fn ro_image_builds() {
        let t = tempfile::tempdir().unwrap();
        let src = t.path().join("src");
        fs::create_dir_all(&src).unwrap();
        fs::write(src.join("x"), vec![7u8; 100_000]).unwrap();
        let st = stage_tree(&src, &t.path().join("s"), &TreeLimits::default()).unwrap();
        let img = t.path().join("x.img");
        build_ro_image(&st, &img).unwrap();
        assert_eq!(fs::metadata(&img).unwrap().mode() & 0o777, 0o444);
        build_scratch_image(&t.path().join("scratch.img"), 64).unwrap();
    }
}
