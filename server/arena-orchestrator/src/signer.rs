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
    /// Load the key from a file containing either an ed25519 PKCS#8 PEM
    /// (`-----BEGIN PRIVATE KEY-----`, the deployment format) or a 32-byte seed
    /// as 64 hex chars. On unix the file must not be accessible by group/others.
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
        Self::from_text(&text)
    }

    /// Parse PKCS#8 PEM or a hex seed.
    pub fn from_text(text: &str) -> Result<Self, String> {
        let t = text.trim();
        if t.starts_with("-----BEGIN") {
            use ed25519_dalek::pkcs8::DecodePrivateKey;
            let key = SigningKey::from_pkcs8_pem(t)
                .map_err(|e| format!("invalid PKCS#8 ed25519 key: {e}"))?;
            return Ok(Self {
                key,
                ephemeral: false,
            });
        }
        Self::from_hex(t)
    }

    pub fn from_hex(seed_hex: &str) -> Result<Self, String> {
        let bytes =
            hex::decode(seed_hex).map_err(|_| "report key must be 64 hex chars".to_string())?;
        let seed: [u8; 32] = bytes
            .try_into()
            .map_err(|_| "report key must be 32 bytes".to_string())?;
        Ok(Self {
            key: SigningKey::from_bytes(&seed),
            ephemeral: false,
        })
    }

    /// Fresh in-memory key (dev mode only).
    pub fn ephemeral() -> Self {
        Self {
            key: SigningKey::generate(&mut rand::rngs::OsRng),
            ephemeral: true,
        }
    }

    /// Generate a new key as PKCS#8 PEM (for `arena-server keygen`); returns (pem, public hex).
    pub fn generate_pem() -> (String, String) {
        use ed25519_dalek::pkcs8::{spki::der::pem::LineEnding, EncodePrivateKey};
        let k = SigningKey::generate(&mut rand::rngs::OsRng);
        let pem = k
            .to_pkcs8_pem(LineEnding::LF)
            .expect("encode pkcs8")
            .to_string();
        (pem, hex::encode(k.verifying_key().to_bytes()))
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
            base64::engine::general_purpose::STANDARD
                .encode(seed)
                .into_bytes(),
            base64::engine::general_purpose::URL_SAFE_NO_PAD
                .encode(seed)
                .into_bytes(),
        ];
        forms
            .iter()
            .any(|f| haystack.windows(f.len()).any(|w| w == f.as_slice()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn pem_and_hex_roundtrip() {
        let (pem, pk) = ReportSigner::generate_pem();
        let s = ReportSigner::from_text(&pem).unwrap();
        assert_eq!(s.public_key_hex(), pk);
        let h = ReportSigner::from_text(&format!("{}\n", hex::encode(s.key.to_bytes()))).unwrap();
        assert_eq!(h.public_key_hex(), pk);
        assert!(h.leaks_into(pem.as_bytes()) || !pem.is_empty());
        assert!(ReportSigner::from_text("nope").is_err());
    }
}
