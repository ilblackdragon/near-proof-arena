//! Content-addressed object store.
//!
//! Objects are keyed by the sha256 [`Digest`] of their raw bytes. Callers never
//! supply paths: the on-disk location is derived exclusively from the
//! validated digest (`objects/<hex[0..2]>/<hex>`). Writes are streamed to a
//! private temp file, hashed while writing, size-bounded, fsynced and then
//! atomically renamed into place, so a reader never observes a partial object
//! and an object's bytes always hash to its key.
//!
//! [`ObjectStore`] is a trait so that an S3 (or other) backend can be added
//! without touching callers.

use arena_types::Digest;
use async_trait::async_trait;
use sha2::{Digest as _, Sha256};
use std::path::{Path, PathBuf};
use std::pin::Pin;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWriteExt};

#[derive(Debug, thiserror::Error)]
pub enum StoreError {
    #[error("object exceeds size limit of {limit} bytes")]
    TooLarge { limit: u64 },
    #[error("content digest mismatch: expected {expected}, got {actual}")]
    DigestMismatch { expected: Digest, actual: Digest },
    #[error("stored object {0} is corrupt")]
    Corrupt(Digest),
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PutOutcome {
    pub digest: Digest,
    pub size: u64,
    /// `false` if an identical object already existed.
    pub newly_created: bool,
}

pub struct ObjectReader {
    pub size: u64,
    pub reader: Pin<Box<dyn AsyncRead + Send>>,
}

/// Streaming writer. Dropping it without `finish` discards the data.
#[async_trait]
pub trait ObjectWriter: Send {
    async fn write(&mut self, chunk: &[u8]) -> Result<(), StoreError>;
    /// Commit the object. If `expected` is given and the content does not hash
    /// to it, nothing is stored and `DigestMismatch` is returned.
    async fn finish(self: Box<Self>, expected: Option<&Digest>) -> Result<PutOutcome, StoreError>;
}

#[async_trait]
pub trait ObjectStore: Send + Sync + 'static {
    /// Upper bound on any single object accepted by this store.
    fn max_object_bytes(&self) -> u64;
    /// Begin a streaming write limited to `min(limit, max_object_bytes)`.
    async fn writer(&self, limit: u64) -> Result<Box<dyn ObjectWriter>, StoreError>;
    async fn open(&self, digest: &Digest) -> Result<Option<ObjectReader>, StoreError>;
    async fn size(&self, digest: &Digest) -> Result<Option<u64>, StoreError>;

    async fn exists(&self, digest: &Digest) -> Result<bool, StoreError> {
        Ok(self.size(digest).await?.is_some())
    }

    async fn put_bytes(
        &self,
        bytes: &[u8],
        expected: Option<&Digest>,
    ) -> Result<PutOutcome, StoreError> {
        let mut w = self.writer(bytes.len() as u64).await?;
        w.write(bytes).await?;
        w.finish(expected).await
    }

    /// Read a whole object into memory, refusing objects larger than `max`.
    /// Content is re-hashed; a mismatch is reported as `Corrupt`.
    async fn get_bytes(&self, digest: &Digest, max: u64) -> Result<Option<Vec<u8>>, StoreError> {
        let Some(mut r) = self.open(digest).await? else {
            return Ok(None);
        };
        if r.size > max {
            return Err(StoreError::TooLarge { limit: max });
        }
        let mut buf = Vec::with_capacity(r.size as usize);
        r.reader
            .as_mut()
            .take(max + 1)
            .read_to_end(&mut buf)
            .await?;
        if buf.len() as u64 > max {
            return Err(StoreError::TooLarge { limit: max });
        }
        if Digest::of_bytes(&buf) != *digest {
            return Err(StoreError::Corrupt(digest.clone()));
        }
        Ok(Some(buf))
    }
}

/// Local filesystem backend.
pub struct FsStore {
    root: PathBuf,
    max_object_bytes: u64,
}

impl FsStore {
    /// Opens (creating if needed) a store rooted at `root`.
    pub fn open(root: impl AsRef<Path>, max_object_bytes: u64) -> Result<Self, StoreError> {
        let root = root.as_ref().to_path_buf();
        std::fs::create_dir_all(root.join("objects"))?;
        std::fs::create_dir_all(root.join("tmp"))?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(root.join("tmp"), std::fs::Permissions::from_mode(0o700))?;
        }
        Ok(Self {
            root,
            max_object_bytes,
        })
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Path for a digest. Only ever derived from a validated `Digest`.
    fn object_path(&self, digest: &Digest) -> PathBuf {
        let hex = digest.hex();
        debug_assert!(hex.len() == 64 && hex.bytes().all(|b| b.is_ascii_hexdigit()));
        self.root.join("objects").join(&hex[..2]).join(hex)
    }

    /// Re-hash a stored object (scrubbing).
    pub async fn verify(&self, digest: &Digest) -> Result<bool, StoreError> {
        let Some(mut r) = self.open(digest).await? else {
            return Ok(false);
        };
        let mut h = Sha256::new();
        let mut buf = vec![0u8; 1 << 16];
        loop {
            let n = r.reader.read(&mut buf).await?;
            if n == 0 {
                break;
            }
            h.update(&buf[..n]);
        }
        Ok(format!("sha256:{}", hex::encode(h.finalize())) == digest.as_str())
    }
}

struct FsWriter {
    tmp: Option<PathBuf>,
    file: Option<tokio::fs::File>,
    hasher: Sha256,
    written: u64,
    limit: u64,
    objects_dir: PathBuf,
}

impl Drop for FsWriter {
    fn drop(&mut self) {
        if let Some(p) = self.tmp.take() {
            let _ = std::fs::remove_file(p);
        }
    }
}

#[async_trait]
impl ObjectWriter for FsWriter {
    async fn write(&mut self, chunk: &[u8]) -> Result<(), StoreError> {
        let new_len = self.written + chunk.len() as u64;
        if new_len > self.limit {
            return Err(StoreError::TooLarge { limit: self.limit });
        }
        self.hasher.update(chunk);
        self.file
            .as_mut()
            .expect("writer used after finish")
            .write_all(chunk)
            .await?;
        self.written = new_len;
        Ok(())
    }

    async fn finish(
        mut self: Box<Self>,
        expected: Option<&Digest>,
    ) -> Result<PutOutcome, StoreError> {
        let mut file = self.file.take().expect("finish called once");
        file.flush().await?;
        file.sync_all().await?;
        drop(file);
        let hasher = std::mem::take(&mut self.hasher);
        let digest = Digest::try_from(format!("sha256:{}", hex::encode(hasher.finalize())))
            .expect("sha256 hex is a valid digest");
        if let Some(exp) = expected {
            if *exp != digest {
                return Err(StoreError::DigestMismatch {
                    expected: exp.clone(),
                    actual: digest,
                });
            }
        }
        let hex = digest.hex();
        let dir = self.objects_dir.join(&hex[..2]);
        tokio::fs::create_dir_all(&dir).await?;
        let dest = dir.join(hex);
        let tmp = self.tmp.take().expect("tmp present until finish");
        let newly_created = if tokio::fs::try_exists(&dest).await? {
            let _ = tokio::fs::remove_file(&tmp).await;
            false
        } else {
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                tokio::fs::set_permissions(&tmp, std::fs::Permissions::from_mode(0o444)).await?;
            }
            tokio::fs::rename(&tmp, &dest).await?;
            // Persist the rename.
            if let Ok(d) = tokio::fs::File::open(&dir).await {
                let _ = d.sync_all().await;
            }
            true
        };
        Ok(PutOutcome {
            digest,
            size: self.written,
            newly_created,
        })
    }
}

#[async_trait]
impl ObjectStore for FsStore {
    fn max_object_bytes(&self) -> u64 {
        self.max_object_bytes
    }

    async fn writer(&self, limit: u64) -> Result<Box<dyn ObjectWriter>, StoreError> {
        let tmp = self
            .root
            .join("tmp")
            .join(format!("{}.part", uuid::Uuid::new_v4().simple()));
        let file = tokio::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&tmp)
            .await?;
        Ok(Box::new(FsWriter {
            tmp: Some(tmp),
            file: Some(file),
            hasher: Sha256::new(),
            written: 0,
            limit: limit.min(self.max_object_bytes),
            objects_dir: self.root.join("objects"),
        }))
    }

    async fn open(&self, digest: &Digest) -> Result<Option<ObjectReader>, StoreError> {
        match tokio::fs::File::open(self.object_path(digest)).await {
            Ok(f) => {
                let size = f.metadata().await?.len();
                Ok(Some(ObjectReader {
                    size,
                    reader: Box::pin(f),
                }))
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(e.into()),
        }
    }

    async fn size(&self, digest: &Digest) -> Result<Option<u64>, StoreError> {
        match tokio::fs::metadata(self.object_path(digest)).await {
            Ok(m) => Ok(Some(m.len())),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(e.into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn roundtrip_and_dedupe() {
        let dir = tempfile::tempdir().unwrap();
        let s = FsStore::open(dir.path(), 1024).unwrap();
        let a = s.put_bytes(b"hello", None).await.unwrap();
        assert!(a.newly_created);
        assert_eq!(a.digest, Digest::of_bytes(b"hello"));
        let b = s.put_bytes(b"hello", Some(&a.digest)).await.unwrap();
        assert!(!b.newly_created);
        assert_eq!(
            s.get_bytes(&a.digest, 100).await.unwrap().unwrap(),
            b"hello"
        );
        assert!(s.verify(&a.digest).await.unwrap());
        assert_eq!(s.size(&Digest::of_bytes(b"nope")).await.unwrap(), None);
        // no temp files left behind
        assert_eq!(
            std::fs::read_dir(dir.path().join("tmp")).unwrap().count(),
            0
        );
    }

    #[tokio::test]
    async fn size_limit_and_mismatch() {
        let dir = tempfile::tempdir().unwrap();
        let s = FsStore::open(dir.path(), 8).unwrap();
        assert!(matches!(
            s.put_bytes(b"123456789", None).await,
            Err(StoreError::TooLarge { .. })
        ));
        let mut w = s.writer(4).await.unwrap();
        w.write(b"1234").await.unwrap();
        assert!(matches!(
            w.write(b"5").await,
            Err(StoreError::TooLarge { limit: 4 })
        ));
        drop(w);
        let wrong = Digest::of_bytes(b"other");
        assert!(matches!(
            s.put_bytes(b"abc", Some(&wrong)).await,
            Err(StoreError::DigestMismatch { .. })
        ));
        assert!(!s.exists(&Digest::of_bytes(b"abc")).await.unwrap());
        assert_eq!(
            std::fs::read_dir(dir.path().join("tmp")).unwrap().count(),
            0
        );
    }

    #[tokio::test]
    async fn detects_corruption() {
        let dir = tempfile::tempdir().unwrap();
        let s = FsStore::open(dir.path(), 1024).unwrap();
        let a = s.put_bytes(b"data", None).await.unwrap();
        let p = s.object_path(&a.digest);
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o644)).unwrap();
        }
        std::fs::write(&p, b"evil").unwrap();
        assert!(matches!(
            s.get_bytes(&a.digest, 100).await,
            Err(StoreError::Corrupt(_))
        ));
        assert!(!s.verify(&a.digest).await.unwrap());
    }
}
