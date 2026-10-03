//! `TreeDigest` (CONTRACTS §1) and helpers to hash / pack on-disk trees.
//!
//! Algorithm (normative for this implementation):
//!
//! 1. Collect every regular file in the tree as
//!    `(relative_path_utf8, mode, content_digest)` where `mode` is `"exec"` if
//!    any execute bit is set and `"file"` otherwise, and `content_digest` is
//!    the `sha256:<hex>` [`Digest`] of the file bytes.
//! 2. Directories are not entries (an empty directory does not change the
//!    digest). Symlinks, hardlinks, devices, fifos, sockets, absolute or `..`
//!    paths are rejected before hashing.
//! 3. Sort entries by the UTF-8 bytes of the path.
//! 4. Serialize as a canonical-JSON array of 3-element arrays, e.g.
//!    `[["a/b","file","sha256:…"],["run","exec","sha256:…"]]`.
//! 5. `TreeDigest = Digest::of_bytes(that JSON)`.

use crate::path::{check_relpath, collision_key};
use crate::{ArchiveError, Limits};
use arena_types::Digest;
use sha2::{Digest as _, Sha256};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::Path;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum FileMode {
    File,
    Exec,
}

impl FileMode {
    pub fn as_str(self) -> &'static str {
        match self {
            FileMode::File => "file",
            FileMode::Exec => "exec",
        }
    }
    pub fn from_unix(mode: u32) -> Self {
        if mode & 0o111 != 0 {
            FileMode::Exec
        } else {
            FileMode::File
        }
    }
    /// Permissions used when materializing a file of this mode.
    pub fn unix_perms(self) -> u32 {
        match self {
            FileMode::File => 0o644,
            FileMode::Exec => 0o755,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeFile {
    pub mode: FileMode,
    pub digest: Digest,
    pub size: u64,
}

/// A validated file tree: regular files with their modes and digests, plus
/// the set of directories (explicit or implied).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Tree {
    pub files: BTreeMap<String, TreeFile>,
    pub dirs: BTreeSet<String>,
}

impl Tree {
    /// The `TreeDigest` of this tree.
    pub fn digest(&self) -> Digest {
        let entries: Vec<(&str, &str, &str)> = self
            .files
            .iter()
            .map(|(p, f)| (p.as_str(), f.mode.as_str(), f.digest.as_str()))
            .collect();
        let bytes = arena_types::canonical_json(&entries).expect("tree entries are float-free");
        Digest::of_bytes(&bytes)
    }

    pub fn total_bytes(&self) -> u64 {
        self.files.values().map(|f| f.size).sum()
    }

    pub fn is_file(&self, p: &str) -> bool {
        self.files.contains_key(p)
    }
    pub fn is_exec(&self, p: &str) -> bool {
        self.files.get(p).map(|f| f.mode == FileMode::Exec).unwrap_or(false)
    }
    pub fn is_dir(&self, p: &str) -> bool {
        self.dirs.contains(p)
    }
    /// True if `p` is a file, or a directory containing at least one file.
    pub fn has_content_at(&self, p: &str) -> bool {
        if self.is_file(p) {
            return true;
        }
        let prefix = format!("{p}/");
        self.files.keys().any(|k| k.starts_with(&prefix))
    }

    /// Restrict to the given roots (files or directories). Paths are
    /// re-rooted unchanged.
    pub fn subset(&self, roots: &[&str]) -> Tree {
        let under = |k: &str| {
            roots.iter().any(|r| k == *r || (k.len() > r.len() && k.starts_with(r) && k.as_bytes()[r.len()] == b'/'))
        };
        let files: BTreeMap<_, _> = self.files.iter().filter(|(k, _)| under(k)).map(|(k, v)| (k.clone(), v.clone())).collect();
        let mut dirs = BTreeSet::new();
        for k in files.keys() {
            for a in crate::path::ancestors(k) {
                dirs.insert(a.to_string());
            }
        }
        for d in &self.dirs {
            if under(d) {
                dirs.insert(d.clone());
            }
        }
        Tree { files, dirs }
    }
}

/// Incremental builder enforcing structural invariants shared by archive
/// ingestion and directory walks: no duplicates, no case/normalization
/// collisions, no file-vs-directory conflicts.
#[derive(Default)]
pub(crate) struct TreeBuilder {
    pub tree: Tree,
    seen_explicit: BTreeSet<String>,
    collisions: HashMap<String, String>,
}

impl TreeBuilder {
    fn note_collision(&mut self, p: &str) -> Result<(), ArchiveError> {
        let key = collision_key(p);
        match self.collisions.get(&key) {
            Some(prev) if prev != p => Err(ArchiveError::unsafe_(format!("case/normalization collision: {prev:?} vs {p:?}"))),
            _ => {
                self.collisions.insert(key, p.to_string());
                Ok(())
            }
        }
    }

    /// Register an explicit entry. Returns the list of ancestor directories
    /// that were not known before (so the caller can create them).
    pub fn add(&mut self, p: &str, is_dir: bool) -> Result<Vec<String>, ArchiveError> {
        check_relpath(p).map_err(ArchiveError::unsafe_)?;
        if !self.seen_explicit.insert(p.to_string()) {
            return Err(ArchiveError::unsafe_(format!("duplicate entry {p:?}")));
        }
        let mut new_dirs = Vec::new();
        for a in crate::path::ancestors(p) {
            if self.tree.files.contains_key(a) {
                return Err(ArchiveError::unsafe_(format!("{p:?} is beneath file {a:?}")));
            }
            if !self.tree.dirs.contains(a) {
                self.note_collision(a)?;
                self.tree.dirs.insert(a.to_string());
                new_dirs.push(a.to_string());
            }
        }
        if is_dir {
            if self.tree.files.contains_key(p) {
                return Err(ArchiveError::unsafe_(format!("directory {p:?} conflicts with file")));
            }
            if self.tree.dirs.insert(p.to_string()) {
                self.note_collision(p)?;
                new_dirs.push(p.to_string());
            }
        } else {
            if self.tree.dirs.contains(p) {
                return Err(ArchiveError::unsafe_(format!("file {p:?} conflicts with directory")));
            }
            self.note_collision(p)?;
        }
        Ok(new_dirs)
    }

    pub fn set_file(&mut self, p: String, f: TreeFile) {
        self.tree.files.insert(p, f);
    }
}

/// Hash an on-disk directory tree without following symlinks.
///
/// Rejects symlinks and special files anywhere in the tree, and enforces
/// `limits.max_entries` / `limits.max_expanded_bytes`.
pub fn tree_from_dir(root: &Path, limits: &Limits) -> Result<Tree, ArchiveError> {
    let meta = fs::symlink_metadata(root)?;
    if !meta.is_dir() {
        return Err(ArchiveError::unsafe_(format!("{} is not a directory", root.display())));
    }
    let mut b = TreeBuilder::default();
    let mut entries = 0u64;
    let mut total = 0u64;
    walk(root, "", &mut b, limits, &mut entries, &mut total)?;
    Ok(b.tree)
}

fn walk(
    dir: &Path,
    rel: &str,
    b: &mut TreeBuilder,
    limits: &Limits,
    entries: &mut u64,
    total: &mut u64,
) -> Result<(), ArchiveError> {
    let mut names = Vec::new();
    for e in fs::read_dir(dir)? {
        let e = e?;
        let name = e
            .file_name()
            .into_string()
            .map_err(|n| ArchiveError::unsafe_(format!("non-UTF-8 file name {n:?}")))?;
        names.push(name);
    }
    names.sort();
    for name in names {
        *entries += 1;
        if *entries > limits.max_entries {
            return Err(ArchiveError::unsafe_(format!("more than {} entries", limits.max_entries)));
        }
        let child_rel = if rel.is_empty() { name.clone() } else { format!("{rel}/{name}") };
        let path = dir.join(&name);
        let meta = fs::symlink_metadata(&path)?;
        let ft = meta.file_type();
        if ft.is_dir() {
            b.add(&child_rel, true)?;
            walk(&path, &child_rel, b, limits, entries, total)?;
        } else if ft.is_file() {
            if meta.nlink() > 1 {
                return Err(ArchiveError::unsafe_(format!("hardlinked file {child_rel:?}")));
            }
            if meta.mode() & 0o7000 != 0 {
                return Err(ArchiveError::unsafe_(format!("setuid/setgid/sticky bit on {child_rel:?}")));
            }
            b.add(&child_rel, false)?;
            let (digest, size) = hash_file_nofollow(&path, limits.max_expanded_bytes - *total)?;
            *total += size;
            b.set_file(child_rel, TreeFile { mode: FileMode::from_unix(meta.mode()), digest, size });
        } else {
            return Err(ArchiveError::unsafe_(format!("{child_rel:?} is not a regular file or directory")));
        }
    }
    Ok(())
}

pub(crate) fn open_nofollow(path: &Path) -> io::Result<File> {
    fs::OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC).open(path)
}

fn hash_file_nofollow(path: &Path, budget: u64) -> Result<(Digest, u64), ArchiveError> {
    let mut f = open_nofollow(path)?;
    let mut h = Sha256::new();
    let mut buf = vec![0u8; 64 * 1024];
    let mut n_total = 0u64;
    loop {
        let n = f.read(&mut buf)?;
        if n == 0 {
            break;
        }
        n_total += n as u64;
        if n_total > budget {
            return Err(ArchiveError::unsafe_("tree exceeds expanded size limit"));
        }
        h.update(&buf[..n]);
    }
    Ok((Digest::try_from(format!("sha256:{}", hex_lower(&h.finalize()))).expect("valid"), n_total))
}

pub(crate) fn hex_lower(b: &[u8]) -> String {
    const H: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(b.len() * 2);
    for x in b {
        s.push(H[(x >> 4) as usize] as char);
        s.push(H[(x & 15) as usize] as char);
    }
    s
}

/// Write a deterministic tar of `tree` (as found under `root`) to `out`:
/// sorted paths, uid/gid 0, mtime 0, perms 0755/0644, directories included.
/// Each file's content is re-hashed while packing and must match `tree`.
pub fn pack_tree<W: Write>(root: &Path, tree: &Tree, out: W) -> Result<W, ArchiveError> {
    let mut all: Vec<(&str, Option<&TreeFile>)> = tree.dirs.iter().map(|d| (d.as_str(), None)).collect();
    all.extend(tree.files.iter().map(|(p, f)| (p.as_str(), Some(f))));
    all.sort_by(|a, b| a.0.cmp(b.0));
    let mut builder = tar::Builder::new(out);
    for (p, f) in all {
        let mut h = tar::Header::new_gnu();
        h.set_uid(0);
        h.set_gid(0);
        h.set_mtime(0);
        match f {
            None => {
                h.set_entry_type(tar::EntryType::Directory);
                h.set_mode(0o755);
                h.set_size(0);
                builder.append_data(&mut h, format!("{p}/"), io::empty())?;
            }
            Some(f) => {
                let file = open_nofollow(&root.join(p))?;
                let meta = file.metadata()?;
                if !meta.is_file() || meta.len() != f.size {
                    return Err(ArchiveError::unsafe_(format!("{p:?} changed while packing")));
                }
                h.set_entry_type(tar::EntryType::Regular);
                h.set_mode(f.mode.unix_perms());
                h.set_size(f.size);
                let mut hr = HashingReader { inner: file.take(f.size), h: Sha256::new() };
                builder.append_data(&mut h, p, &mut hr)?;
                let got = format!("sha256:{}", hex_lower(&hr.h.finalize()));
                if got != f.digest.as_str() {
                    return Err(ArchiveError::unsafe_(format!("{p:?} changed while packing")));
                }
            }
        }
    }
    Ok(builder.into_inner()?)
}

struct HashingReader<R> {
    inner: R,
    h: Sha256,
}
impl<R: Read> Read for HashingReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.inner.read(buf)?;
        self.h.update(&buf[..n]);
        Ok(n)
    }
}

/// Set permissions on a materialized file according to its mode.
pub(crate) fn set_mode(f: &File, mode: FileMode) -> io::Result<()> {
    f.set_permissions(fs::Permissions::from_mode(mode.unix_perms()))
}
