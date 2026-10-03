//! Content-addressed artifact access. Every fetched blob is re-hashed and
//! must equal the requested digest.

use arena_types::Digest;
use std::fs;
use std::io;
use std::path::PathBuf;

#[derive(Debug, thiserror::Error)]
pub enum StoreError {
    #[error("artifact {0} not found")]
    NotFound(Digest),
    #[error("artifact {want} content mismatch (got {got})")]
    Corrupt { want: Digest, got: Digest },
    #[error("artifact {0} larger than {1} bytes")]
    TooLarge(Digest, u64),
    #[error("store transport: {0}")]
    Transport(String),
    #[error("io: {0}")]
    Io(#[from] io::Error),
}

pub trait ArtifactStore: Send + Sync {
    /// Fetch raw bytes (at most `max_bytes`).
    fn get_raw(&self, digest: &Digest, max_bytes: u64) -> Result<Vec<u8>, StoreError>;
    fn put(&self, bytes: &[u8]) -> Result<Digest, StoreError>;

    /// Fetch and verify.
    fn get(&self, digest: &Digest, max_bytes: u64) -> Result<Vec<u8>, StoreError> {
        let b = self.get_raw(digest, max_bytes)?;
        if b.len() as u64 > max_bytes {
            return Err(StoreError::TooLarge(digest.clone(), max_bytes));
        }
        let got = Digest::of_bytes(&b);
        if &got != digest {
            return Err(StoreError::Corrupt {
                want: digest.clone(),
                got,
            });
        }
        Ok(b)
    }
}

/// Directory-backed store (`<root>/<hex>`), for local runs and tests.
pub struct FsStore {
    pub root: PathBuf,
}

impl FsStore {
    pub fn new(root: impl Into<PathBuf>) -> io::Result<Self> {
        let root = root.into();
        fs::create_dir_all(&root)?;
        Ok(FsStore { root })
    }
}

impl ArtifactStore for FsStore {
    fn get_raw(&self, digest: &Digest, max_bytes: u64) -> Result<Vec<u8>, StoreError> {
        let p = self.root.join(digest.hex());
        match fs::metadata(&p) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                Err(StoreError::NotFound(digest.clone()))
            }
            Err(e) => Err(e.into()),
            Ok(m) if m.len() > max_bytes => Err(StoreError::TooLarge(digest.clone(), max_bytes)),
            Ok(_) => Ok(fs::read(p)?),
        }
    }
    fn put(&self, bytes: &[u8]) -> Result<Digest, StoreError> {
        let d = Digest::of_bytes(bytes);
        let p = self.root.join(d.hex());
        if !p.exists() {
            let tmp = self
                .root
                .join(format!(".tmp-{}-{}", d.hex(), std::process::id()));
            fs::write(&tmp, bytes)?;
            fs::rename(tmp, p)?;
        }
        Ok(d)
    }
}
