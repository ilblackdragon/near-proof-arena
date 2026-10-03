//! Safe ingestion of candidate packages (CONTRACTS §1, §3).
//!
//! [`ingest`] streams a `tar` or `tar.zst` archive and extracts it into a
//! freshly created directory, rejecting anything that is not a plain regular
//! file or directory with a safe relative path. All limits are enforced with
//! streaming counters so hostile archives are aborted early, before their
//! declared or decompressed size is materialized. The result carries the
//! [`TreeDigest`](tree) of the extracted tree.
//!
//! [`package::validate_package`] then checks `candidate.toml` and the package
//! layout against the extracted tree (not against the filesystem, so there is
//! no TOCTOU window).

pub mod package;
pub mod path;
pub mod tree;

pub use package::{validate_package, PackageError};
pub use tree::{pack_tree, tree_from_dir, FileMode, Tree, TreeFile};

use sha2::{Digest as _, Sha256};
use std::cell::Cell;
use std::fs;
use std::io::{self, BufRead, BufReader, Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::rc::Rc;

/// Ingestion limits. Defaults follow CONTRACTS §3.
#[derive(Clone, Debug)]
pub struct Limits {
    pub max_compressed_bytes: u64,
    pub max_expanded_bytes: u64,
    pub max_entries: u64,
    /// Maximum ratio of decompressed tar stream bytes to compressed bytes
    /// consumed so far (checked continuously once past `ratio_slack_bytes`).
    pub max_ratio: u64,
    pub ratio_slack_bytes: u64,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            max_compressed_bytes: 256 << 20,
            max_expanded_bytes: 2 << 30,
            max_entries: 100_000,
            max_ratio: 200,
            ratio_slack_bytes: 16 << 20,
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ArchiveError {
    /// The archive (or tree) is malformed or violates a safety rule. Maps to
    /// reason code `ARCHIVE_UNSAFE`. Never retried.
    #[error("unsafe archive: {0}")]
    Unsafe(String),
    /// Local I/O failure on the judge side (disk full, permissions, ...).
    /// Maps to `INFRA_ERROR`.
    #[error("io: {0}")]
    Io(#[from] io::Error),
}

impl ArchiveError {
    pub fn unsafe_(s: impl Into<String>) -> Self {
        ArchiveError::Unsafe(s.into())
    }
    pub fn is_unsafe(&self) -> bool {
        matches!(self, ArchiveError::Unsafe(_))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Compression {
    None,
    Zstd,
}

/// Result of a successful ingestion.
#[derive(Debug)]
pub struct Extracted {
    pub root: PathBuf,
    pub tree: Tree,
    pub digest: arena_types::Digest,
    pub compression: Compression,
    pub compressed_bytes: u64,
}

const ZSTD_MAGIC: [u8; 4] = [0x28, 0xb5, 0x2f, 0xfd];

#[derive(Clone)]
struct Counter(Rc<Cell<u64>>);
impl Counter {
    fn new() -> Self {
        Counter(Rc::new(Cell::new(0)))
    }
    fn get(&self) -> u64 {
        self.0.get()
    }
}

/// Reader that counts bytes and refuses to read past `limit`.
struct CountingReader<R> {
    inner: R,
    count: Counter,
    limit: u64,
    what: &'static str,
}
impl<R: Read> Read for CountingReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.inner.read(buf)?;
        let c = self.count.get() + n as u64;
        self.count.0.set(c);
        if c > self.limit {
            return Err(io::Error::other(LimitExceeded(self.what)));
        }
        Ok(n)
    }
}

#[derive(Debug)]
struct LimitExceeded(&'static str);
impl std::fmt::Display for LimitExceeded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} limit exceeded", self.0)
    }
}
impl std::error::Error for LimitExceeded {}

/// Any error from the read side (decompressor / tar parser / our counters)
/// is an archive problem, never an infra problem.
fn read_err(e: io::Error) -> ArchiveError {
    ArchiveError::Unsafe(format!("malformed archive: {e}"))
}

/// Ingest an archive from bytes. See [`ingest`].
pub fn ingest_bytes(bytes: &[u8], dest: &Path, limits: &Limits) -> Result<Extracted, ArchiveError> {
    if bytes.len() as u64 > limits.max_compressed_bytes {
        return Err(ArchiveError::unsafe_(
            "archive exceeds compressed size limit",
        ));
    }
    ingest(bytes, dest, limits)
}

/// Stream-ingest a `tar` or `tar.zst` archive into `dest`, which must not
/// exist (it is created with mode 0700). On error `dest` is removed.
pub fn ingest<R: Read>(input: R, dest: &Path, limits: &Limits) -> Result<Extracted, ArchiveError> {
    fs::DirBuilder::new().mode(0o700).create(dest)?;
    match ingest_inner(input, dest, limits) {
        Ok(x) => Ok(x),
        Err(e) => {
            let _ = fs::remove_dir_all(dest);
            Err(e)
        }
    }
}

fn ingest_inner<R: Read>(
    input: R,
    dest: &Path,
    limits: &Limits,
) -> Result<Extracted, ArchiveError> {
    let compressed = Counter::new();
    let raw = CountingReader {
        inner: input,
        count: compressed.clone(),
        limit: limits.max_compressed_bytes,
        what: "compressed size",
    };
    let mut raw = BufReader::new(raw);
    let head = raw.fill_buf().map_err(read_err)?;
    let compression = if head.len() >= 4 && head[..4] == ZSTD_MAGIC {
        Compression::Zstd
    } else {
        Compression::None
    };

    // Upper bound on the decompressed tar stream: content + 512-byte header
    // and padding per entry (+ long-name / pax records), generously bounded.
    let stream_limit = limits
        .max_expanded_bytes
        .saturating_add(limits.max_entries.saturating_mul(4 * 512))
        .saturating_add(1 << 20);
    let decompressed = Counter::new();
    let tar_stream: Box<dyn Read> = match compression {
        Compression::Zstd => {
            let mut dec = zstd::stream::read::Decoder::with_buffer(raw).map_err(read_err)?;
            // 2^27 = 128 MiB maximum window: bounds decoder memory.
            dec.window_log_max(27).map_err(read_err)?;
            Box::new(dec)
        }
        Compression::None => Box::new(raw),
    };
    let tar_stream = CountingReader {
        inner: tar_stream,
        count: decompressed.clone(),
        limit: stream_limit,
        what: "decompressed stream",
    };

    let check_ratio = |dec: u64, comp: u64| -> Result<(), ArchiveError> {
        if dec > limits.ratio_slack_bytes && dec > comp.saturating_mul(limits.max_ratio) {
            return Err(ArchiveError::unsafe_(format!(
                "compression ratio exceeds {}:1 ({} bytes from {} compressed)",
                limits.max_ratio, dec, comp
            )));
        }
        Ok(())
    };

    let mut archive = tar::Archive::new(tar_stream);
    let mut builder = tree::TreeBuilder::default();
    let mut n_entries = 0u64;
    let mut expanded = 0u64;
    let mut buf = vec![0u8; 64 * 1024];

    for entry in archive.entries().map_err(read_err)? {
        let mut entry = entry.map_err(read_err)?;
        n_entries += 1;
        if n_entries > limits.max_entries {
            return Err(ArchiveError::unsafe_(format!(
                "more than {} entries",
                limits.max_entries
            )));
        }
        check_ratio(decompressed.get(), compressed.get())?;
        let ety = entry.header().entry_type();
        let is_dir = match ety {
            tar::EntryType::Regular => false,
            tar::EntryType::Directory => true,
            // Global pax headers carry no per-file data we honour.
            tar::EntryType::XGlobalHeader => continue,
            tar::EntryType::Symlink => return Err(ArchiveError::unsafe_("symlink entry")),
            tar::EntryType::Link => return Err(ArchiveError::unsafe_("hardlink entry")),
            tar::EntryType::Char | tar::EntryType::Block => {
                return Err(ArchiveError::unsafe_("device entry"))
            }
            tar::EntryType::Fifo => return Err(ArchiveError::unsafe_("fifo entry")),
            other => {
                return Err(ArchiveError::unsafe_(format!(
                    "unsupported entry type {other:?}"
                )))
            }
        };
        let raw_path = entry.path_bytes().into_owned();
        let Some(rel) = path::normalize(&raw_path).map_err(ArchiveError::Unsafe)? else {
            if is_dir {
                continue;
            }
            return Err(ArchiveError::unsafe_("file entry for archive root"));
        };
        let mode = entry.header().mode().map_err(read_err)?;
        if mode & 0o7000 != 0 {
            return Err(ArchiveError::unsafe_(format!(
                "setuid/setgid/sticky bit on {rel:?}"
            )));
        }
        let new_dirs = builder.add(&rel, is_dir)?;
        for d in &new_dirs {
            fs::DirBuilder::new().mode(0o755).create(dest.join(d))?;
        }
        if is_dir {
            if entry.size() != 0 {
                return Err(ArchiveError::unsafe_(format!(
                    "directory {rel:?} with data"
                )));
            }
            continue;
        }
        let size = entry.size();
        if expanded.saturating_add(size) > limits.max_expanded_bytes {
            return Err(ArchiveError::unsafe_("archive exceeds expanded size limit"));
        }
        let mut out = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(dest.join(&rel))?;
        let mut h = Sha256::new();
        let mut copied = 0u64;
        loop {
            let n = entry.read(&mut buf).map_err(read_err)?;
            if n == 0 {
                break;
            }
            copied += n as u64;
            if copied > size {
                return Err(ArchiveError::unsafe_(format!(
                    "{rel:?} longer than declared"
                )));
            }
            h.update(&buf[..n]);
            out.write_all(&buf[..n])?;
            check_ratio(decompressed.get(), compressed.get())?;
        }
        if copied != size {
            return Err(ArchiveError::unsafe_(format!("{rel:?} truncated")));
        }
        expanded += size;
        let fmode = FileMode::from_unix(mode);
        tree::set_mode(&out, fmode)?;
        let digest =
            arena_types::Digest::try_from(format!("sha256:{}", tree::hex_lower(&h.finalize())))
                .expect("valid digest");
        builder.set_file(
            rel,
            TreeFile {
                mode: fmode,
                digest,
                size,
            },
        );
    }
    check_ratio(decompressed.get(), compressed.get())?;
    let tree = builder.tree;
    let digest = tree.digest();
    Ok(Extracted {
        root: dest.to_path_buf(),
        tree,
        digest,
        compression,
        compressed_bytes: compressed.get(),
    })
}

#[cfg(test)]
mod tests;
