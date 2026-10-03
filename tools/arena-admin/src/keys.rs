//! Governance ed25519 keys.
//!
//! * Public key file (`*.pub`, committed): JSON [`PublicKeyFile`].
//! * Private key file (never committed): JSON [`PrivateKeyFile`], mode 0600.
//!   Production keys are meant to live offline / in an HSM; see
//!   `docs/SECURITY_POLICY.md`. This module refuses to write a private key
//!   inside a git working tree and refuses to read one that is group/other
//!   readable.
//!
//! Signatures are plain ed25519 (RFC 8032) over the exact JCS bytes of the
//! signed object, stored as one line of lowercase hex (128 chars) in a
//! detached `.sig` file.

use anyhow::{bail, Context, Result};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

pub const PUBKEY_SCHEMA: &str = "arena-governance-pubkey-v1";
pub const PRIVKEY_SCHEMA: &str = "arena-governance-privkey-v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PublicKeyFile {
    pub schema: String,
    pub algorithm: String,
    /// `gov_` + first 16 hex chars of sha256(public key bytes).
    pub key_id: String,
    pub public_key_hex: String,
    /// A dev-only key may sign `demo`/`experimental` challenges only; the
    /// verifier rejects `formal` challenges signed by it.
    pub dev_only: bool,
    pub label: String,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PrivateKeyFile {
    pub schema: String,
    pub algorithm: String,
    pub key_id: String,
    /// 32-byte ed25519 seed, hex.
    pub seed_hex: String,
    pub dev_only: bool,
    pub label: String,
}

pub fn key_id(vk: &VerifyingKey) -> String {
    format!("gov_{}", &hex::encode(Sha256::digest(vk.as_bytes()))[..16])
}

/// Walk up from `path` looking for a `.git` entry (dir or worktree file).
pub fn inside_git_worktree(path: &Path) -> Option<PathBuf> {
    let abs = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir().ok()?.join(path)
    };
    let mut cur = abs.parent();
    while let Some(dir) = cur {
        if dir.join(".git").exists() {
            return Some(dir.to_path_buf());
        }
        cur = dir.parent();
    }
    None
}

pub struct Keypair {
    pub signing: SigningKey,
    pub dev_only: bool,
    pub label: String,
}

impl Keypair {
    pub fn generate(dev_only: bool, label: &str) -> Self {
        let signing = SigningKey::generate(&mut rand_core::OsRng);
        Keypair {
            signing,
            dev_only,
            label: label.to_string(),
        }
    }

    pub fn public_file(&self) -> PublicKeyFile {
        let vk = self.signing.verifying_key();
        PublicKeyFile {
            schema: PUBKEY_SCHEMA.into(),
            algorithm: "ed25519".into(),
            key_id: key_id(&vk),
            public_key_hex: hex::encode(vk.as_bytes()),
            dev_only: self.dev_only,
            label: self.label.clone(),
        }
    }

    /// Write the private key with mode 0600, failing if the file exists or
    /// if the target is inside a git working tree (unless `allow_in_repo`,
    /// which exists only for tests).
    pub fn write_private(&self, path: &Path, allow_in_repo: bool) -> Result<()> {
        if !allow_in_repo {
            if let Some(repo) = inside_git_worktree(path) {
                bail!(
                    "refusing to write a private key inside git working tree {}; \
                     store governance keys outside any repository (offline media / HSM)",
                    repo.display()
                );
            }
        }
        let vk = self.signing.verifying_key();
        let body = PrivateKeyFile {
            schema: PRIVKEY_SCHEMA.into(),
            algorithm: "ed25519".into(),
            key_id: key_id(&vk),
            seed_hex: hex::encode(self.signing.to_bytes()),
            dev_only: self.dev_only,
            label: self.label.clone(),
        };
        let mut opts = fs::OpenOptions::new();
        opts.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            opts.mode(0o600);
        }
        let mut f = opts.open(path).with_context(|| {
            format!(
                "creating private key file {} (must not exist)",
                path.display()
            )
        })?;
        f.write_all(serde_json::to_string_pretty(&body)?.as_bytes())?;
        f.write_all(b"\n")?;
        f.sync_all()?;
        Ok(())
    }

    pub fn load_private(path: &Path) -> Result<Self> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = fs::metadata(path)
                .with_context(|| format!("stat {}", path.display()))?
                .permissions()
                .mode();
            if mode & 0o077 != 0 {
                bail!(
                    "private key {} has mode {:o}; must not be group/other accessible (chmod 600)",
                    path.display(),
                    mode & 0o777
                );
            }
        }
        let text =
            fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
        let pk: PrivateKeyFile = serde_json::from_str(&text).context("parsing private key file")?;
        if pk.schema != PRIVKEY_SCHEMA || pk.algorithm != "ed25519" {
            bail!("unsupported private key schema/algorithm");
        }
        let seed: [u8; 32] = hex::decode(&pk.seed_hex)?
            .try_into()
            .map_err(|_| anyhow::anyhow!("seed must be 32 bytes"))?;
        let signing = SigningKey::from_bytes(&seed);
        if key_id(&signing.verifying_key()) != pk.key_id {
            bail!("private key file key_id does not match its seed");
        }
        Ok(Keypair {
            signing,
            dev_only: pk.dev_only,
            label: pk.label,
        })
    }

    pub fn sign_hex(&self, msg: &[u8]) -> String {
        hex::encode(self.signing.sign(msg).to_bytes())
    }
}

pub struct PublicKey {
    pub file: PublicKeyFile,
    pub key: VerifyingKey,
}

impl PublicKey {
    pub fn load(path: &Path) -> Result<Self> {
        let text =
            fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
        Self::parse(&text)
    }

    pub fn parse(text: &str) -> Result<Self> {
        let file: PublicKeyFile = serde_json::from_str(text).context("parsing public key file")?;
        if file.schema != PUBKEY_SCHEMA || file.algorithm != "ed25519" {
            bail!("unsupported public key schema/algorithm");
        }
        let bytes: [u8; 32] = hex::decode(&file.public_key_hex)?
            .try_into()
            .map_err(|_| anyhow::anyhow!("public key must be 32 bytes"))?;
        let key = VerifyingKey::from_bytes(&bytes).context("invalid ed25519 public key")?;
        if key_id(&key) != file.key_id {
            bail!("public key file key_id does not match key bytes");
        }
        Ok(PublicKey { file, key })
    }

    /// Verify a detached hex signature (`.sig` file contents). Uses
    /// `verify_strict` (rejects small-order keys / non-canonical encodings).
    pub fn verify_hex(&self, msg: &[u8], sig_text: &str) -> Result<()> {
        let sig_text = sig_text.strip_suffix('\n').unwrap_or(sig_text);
        if sig_text.len() != 128
            || !sig_text
                .bytes()
                .all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
        {
            bail!("signature file must be exactly 128 lowercase hex chars (+ optional newline)");
        }
        let bytes: [u8; 64] = hex::decode(sig_text)?.try_into().unwrap();
        let sig = Signature::from_bytes(&bytes);
        self.key.verify_strict(msg, &sig).map_err(|_| {
            anyhow::anyhow!("signature verification FAILED for key {}", self.file.key_id)
        })
    }
}
