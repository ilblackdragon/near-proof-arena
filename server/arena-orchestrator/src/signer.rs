//! Report signing key. Lives only in the control plane: it is never written to
//! the database, the object store, job payloads, or any API response other
//! than its *public* half.

use ed25519_dalek::{Signer, SigningKey, VerifyingKey};
use std::path::Path;

pub struct ReportSigner {
    key: SigningKey,
    ephemeral: bool,
}

impl std::fmt::Debug for ReportSigner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ReportSigner")
            .field("public_key", &self.public_key_hex())
            .field("ephemeral", &self.ephemeral)
            .finish_non_exhaustive()
    }
}

impl ReportSigner {
    /// Load a 32-byte ed25519 seed stored as 64 hex chars (optionally with whitespace).
    /// On unix the file must not be readable by group/others.
    pub fn from_file(path: &Path) -> Result<Self, String> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let meta = std::fs::metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
            if meta.permissions().mode() & 0o077 != 0 {
                return Err(format!(
                    "{}: report key file must not be accessible by group/others (chmod 600)",
                    path.display()
                ));
            }
        }
        let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        Self::from_hex(text.trim())
    }

    pub fn from_hex(seed_hex: &str) -> Result<Self, String> {
        let bytes = hex::decode(seed_hex).map_err(|_| "report key must be 64 hex chars".to_string())?;
        let seed: [u8; 32] = bytes.try_into().map_err(|_| "report key must be 32 bytes".to_string())?;
        Ok(Self { key: SigningKey::from_bytes(&seed), ephemeral: false })
    }

    /// Fresh in-memory key (dev mode only).
    pub fn ephemeral() -> Self {
        Self { key: SigningKey::generate(&mut rand::rngs::OsRng), ephemeral: true }
    }

    /// Generate a new seed as hex (for `arena-server keygen`).
    pub fn generate_seed_hex() -> String {
        hex::encode(SigningKey::generate(&mut rand::rngs::OsRng).to_bytes())
    }

    pub fn is_ephemeral(&self) -> bool {
        self.ephemeral
    }

    pub fn verifying_key(&self) -> VerifyingKey {
        self.key.verifying_key()
    }

    pub fn public_key_hex(&self) -> String {
        hex::encode(self.key.verifying_key().to_bytes())
    }

    pub fn sign(&self, msg: &[u8]) -> [u8; 64] {
        self.key.sign(msg).to_bytes()
    }

    /// Test helper: whether `haystack` contains the secret seed in raw, hex or base64 form.
    pub fn leaks_into(&self, haystack: &[u8]) -> bool {
        use base64::Engine;
        let seed = self.key.to_bytes();
        let forms: [Vec<u8>; 4] = [
            seed.to_vec(),
            hex::encode(seed).into_bytes(),
            base64::engine::general_purpose::STANDARD.encode(seed).into_bytes(),
            base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(seed).into_bytes(),
        ];
        forms.iter().any(|f| haystack.windows(f.len()).any(|w| w == f.as_slice()))
    }
}
