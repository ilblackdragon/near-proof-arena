//! Canonical JSON (JCS subset: we forbid floats entirely) and digests.

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};
use std::fmt;

#[derive(Debug, thiserror::Error)]
pub enum CanonicalError {
    #[error("floating point numbers are forbidden in canonical objects")]
    Float,
    #[error("serialization: {0}")]
    Serde(#[from] serde_json::Error),
}

/// `sha256:<64 lowercase hex>`
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize, JsonSchema)]
#[serde(try_from = "String", into = "String")]
pub struct Digest(#[schemars(regex(pattern = r"^sha256:[0-9a-f]{64}$"))] String);

impl Digest {
    pub fn of_bytes(bytes: &[u8]) -> Self {
        Digest(format!("sha256:{}", hex::encode(Sha256::digest(bytes))))
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
    pub fn hex(&self) -> &str {
        &self.0["sha256:".len()..]
    }
}

impl TryFrom<String> for Digest {
    type Error = String;
    fn try_from(s: String) -> Result<Self, String> {
        let ok = s.len() == 71
            && s.starts_with("sha256:")
            && s[7..]
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b));
        if ok {
            Ok(Digest(s))
        } else {
            Err(format!("invalid digest: {s:?}"))
        }
    }
}

impl From<Digest> for String {
    fn from(d: Digest) -> String {
        d.0
    }
}

impl fmt::Display for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl fmt::Debug for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Canonical JSON bytes: object keys sorted by UTF-16 code units (equal to
/// byte order for the ASCII keys we use), no whitespace, no floats.
pub fn canonical_json<T: Serialize>(value: &T) -> Result<Vec<u8>, CanonicalError> {
    let v = serde_json::to_value(value)?;
    let mut out = Vec::new();
    write_canonical(&v, &mut out)?;
    Ok(out)
}

fn write_canonical(v: &serde_json::Value, out: &mut Vec<u8>) -> Result<(), CanonicalError> {
    use serde_json::Value;
    match v {
        Value::Null | Value::Bool(_) | Value::String(_) => {
            out.extend_from_slice(serde_json::to_string(v)?.as_bytes())
        }
        Value::Number(n) => {
            if n.is_f64() {
                return Err(CanonicalError::Float);
            }
            out.extend_from_slice(n.to_string().as_bytes())
        }
        Value::Array(a) => {
            out.push(b'[');
            for (i, x) in a.iter().enumerate() {
                if i > 0 {
                    out.push(b',');
                }
                write_canonical(x, out)?;
            }
            out.push(b']');
        }
        Value::Object(m) => {
            let mut keys: Vec<&String> = m.keys().collect();
            keys.sort_by(|a, b| a.encode_utf16().cmp(b.encode_utf16()));
            out.push(b'{');
            for (i, k) in keys.into_iter().enumerate() {
                if i > 0 {
                    out.push(b',');
                }
                out.extend_from_slice(serde_json::to_string(k)?.as_bytes());
                out.push(b':');
                write_canonical(&m[k], out)?;
            }
            out.push(b'}');
        }
    }
    Ok(())
}

pub fn sha256_digest<T: Serialize>(value: &T) -> Result<Digest, CanonicalError> {
    Ok(Digest::of_bytes(&canonical_json(value)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sorted_and_compact() {
        let v = serde_json::json!({"b": 1, "a": [true, null, "x"]});
        assert_eq!(
            canonical_json(&v).unwrap(),
            br#"{"a":[true,null,"x"],"b":1}"#
        );
    }
    #[test]
    fn rejects_float() {
        assert!(canonical_json(&serde_json::json!({"a": 1.5})).is_err());
    }
    #[test]
    fn digest_roundtrip() {
        let d = Digest::of_bytes(b"");
        assert_eq!(
            d.as_str(),
            "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert!(Digest::try_from("sha256:XYZ".to_string()).is_err());
    }
}
