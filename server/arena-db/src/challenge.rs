//! Challenge registration and integrity-checked loading.
//!
//! A challenge is accepted only if its ed25519 signature over the canonical
//! (JCS) bytes of the definition verifies under a configured governance key.
//! Every load re-canonicalizes the stored definition, recomputes id and
//! digest, and re-verifies the signature; any mismatch is an integrity error
//! and the challenge is not served.

use crate::{rfc3339, DbError};
use arena_types::{canonical_json, challenge::Tier, ChallengeDefinition, Digest};
use base64::Engine;
use ed25519_dalek::{Signature, VerifyingKey};
use serde::Serialize;
use sqlx::PgExecutor;
use time::OffsetDateTime;

/// Parse a 32-byte ed25519 public key from hex (64 chars) or base64.
pub fn parse_pubkey(s: &str) -> Result<VerifyingKey, String> {
    let bytes = decode_hex_or_b64(s.trim())?;
    let arr: [u8; 32] = bytes
        .try_into()
        .map_err(|_| "public key must be 32 bytes".to_string())?;
    VerifyingKey::from_bytes(&arr).map_err(|e| format!("invalid public key: {e}"))
}

/// Parse a 64-byte ed25519 signature from hex (128 chars) or base64.
pub fn parse_signature(s: &str) -> Result<Signature, String> {
    let bytes = decode_hex_or_b64(s.trim())?;
    let arr: [u8; 64] = bytes
        .try_into()
        .map_err(|_| "signature must be 64 bytes".to_string())?;
    Ok(Signature::from_bytes(&arr))
}

fn decode_hex_or_b64(s: &str) -> Result<Vec<u8>, String> {
    if s.len().is_multiple_of(2) && s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return hex::decode(s).map_err(|e| e.to_string());
    }
    base64::engine::general_purpose::STANDARD
        .decode(s)
        .or_else(|_| base64::engine::general_purpose::URL_SAFE_NO_PAD.decode(s))
        .map_err(|_| "expected hex or base64".to_string())
}

/// Result of verifying a challenge definition against the governance keys.
#[derive(Clone, Debug)]
pub struct VerifiedChallenge {
    pub id: String,
    pub digest: Digest,
    pub canonical_bytes: Vec<u8>,
    pub signer: VerifyingKey,
    pub signature: Signature,
    pub definition: ChallengeDefinition,
}

/// Verify `sig` over JCS(definition) with any of `keys`, recomputing id/digest.
pub fn verify_definition(
    definition: ChallengeDefinition,
    sig: &Signature,
    keys: &[VerifyingKey],
) -> Result<VerifiedChallenge, String> {
    if definition.schema.is_empty() || definition.name.is_empty() {
        return Err("definition schema/name must be non-empty".into());
    }
    let canonical_bytes = canonical_json(&definition).map_err(|e| e.to_string())?;
    let digest = Digest::of_bytes(&canonical_bytes);
    let id = format!("chl_{}", &digest.hex()[..32]);
    debug_assert_eq!(definition.id().ok().as_deref(), Some(id.as_str()));
    let signer = keys
        .iter()
        .find(|k| k.verify_strict(&canonical_bytes, sig).is_ok())
        .ok_or_else(|| "signature does not verify under any governance key".to_string())?;
    let weights: u64 = definition
        .workload_suite
        .classes
        .iter()
        .map(|c| c.weight_ppm as u64)
        .sum();
    if !definition.workload_suite.classes.is_empty() && weights != 1_000_000 {
        return Err(format!(
            "workload weights sum to {weights} ppm, expected 1000000"
        ));
    }
    Ok(VerifiedChallenge {
        id,
        digest,
        canonical_bytes,
        signer: *signer,
        signature: *sig,
        definition,
    })
}

#[derive(Clone, Debug, Serialize, schemars::JsonSchema)]
pub struct StoredChallenge {
    pub id: String,
    pub digest: Digest,
    pub tier: Tier,
    pub open: bool,
    /// Id of a registered challenge whose `supersedes` names this one. A
    /// superseded challenge is closed for new submissions; its results and
    /// board stay attached to it (docs/PROTOCOL_UPGRADES.md §5).
    pub superseded_by: Option<String>,
    pub registered_by: String,
    pub registered_at: String,
    /// Hex ed25519 governance key that signed the definition.
    pub governance_key: String,
    /// Hex signature over the JCS bytes of `definition`.
    pub signature: String,
    pub definition: ChallengeDefinition,
}

#[derive(sqlx::FromRow)]
struct Row {
    id: String,
    digest: String,
    definition: serde_json::Value,
    canonical_bytes: Vec<u8>,
    signature: Vec<u8>,
    governance_key: Vec<u8>,
    open: bool,
    registered_by: String,
    created_at: OffsetDateTime,
    superseded_by: Option<String>,
}

const COLS: &str = "id, digest, definition, canonical_bytes, signature, governance_key, open, registered_by, created_at,
     (SELECT s.id FROM challenges s WHERE s.definition->>'supersedes' = challenges.id ORDER BY s.created_at, s.id LIMIT 1) AS superseded_by";

fn check_row(r: Row, keys: &[VerifyingKey]) -> Result<StoredChallenge, DbError> {
    let fail = |why: String| DbError::ChallengeIntegrity {
        id: r.id.clone(),
        why,
    };
    let def: ChallengeDefinition = serde_json::from_value(r.definition.clone())
        .map_err(|e| fail(format!("definition: {e}")))?;
    let bytes = canonical_json(&def).map_err(|e| fail(e.to_string()))?;
    if bytes != r.canonical_bytes {
        return Err(fail(
            "stored definition does not match signed canonical bytes".into(),
        ));
    }
    let digest = Digest::of_bytes(&bytes);
    if digest.as_str() != r.digest || format!("chl_{}", &digest.hex()[..32]) != r.id {
        return Err(fail("id/digest mismatch".into()));
    }
    let key_arr: [u8; 32] = r
        .governance_key
        .clone()
        .try_into()
        .map_err(|_| fail("bad key length".into()))?;
    let key = VerifyingKey::from_bytes(&key_arr).map_err(|e| fail(e.to_string()))?;
    if !keys.contains(&key) {
        return Err(fail("signing key is not a trusted governance key".into()));
    }
    let sig_arr: [u8; 64] = r
        .signature
        .clone()
        .try_into()
        .map_err(|_| fail("bad signature length".into()))?;
    let sig = Signature::from_bytes(&sig_arr);
    key.verify_strict(&bytes, &sig)
        .map_err(|_| fail("signature verification failed".into()))?;
    Ok(StoredChallenge {
        id: r.id,
        digest,
        tier: def.tier,
        open: r.open,
        superseded_by: r.superseded_by,
        registered_by: r.registered_by,
        registered_at: rfc3339(r.created_at),
        governance_key: hex::encode(key_arr),
        signature: hex::encode(sig_arr),
        definition: def,
    })
}

/// Load one challenge, verifying its integrity. `Ok(None)` if unknown.
pub async fn load<'e>(
    ex: impl PgExecutor<'e>,
    id: &str,
    keys: &[VerifyingKey],
) -> Result<Option<StoredChallenge>, DbError> {
    let row: Option<Row> = sqlx::query_as(&format!("SELECT {COLS} FROM challenges WHERE id = $1"))
        .bind(id)
        .fetch_optional(ex)
        .await?;
    row.map(|r| check_row(r, keys)).transpose()
}

/// List challenges that pass integrity checks (failures are logged and skipped).
pub async fn list<'e>(
    ex: impl PgExecutor<'e>,
    keys: &[VerifyingKey],
) -> Result<Vec<StoredChallenge>, DbError> {
    let rows: Vec<Row> = sqlx::query_as(&format!(
        "SELECT {COLS} FROM challenges ORDER BY created_at, id"
    ))
    .fetch_all(ex)
    .await?;
    let mut out = Vec::with_capacity(rows.len());
    for r in rows {
        match check_row(r, keys) {
            Ok(c) => out.push(c),
            Err(e) => tracing::error!("refusing to serve challenge: {e}"),
        }
    }
    Ok(out)
}

pub enum RegisterOutcome {
    Created {
        /// The predecessor (`supersedes`) that this registration closed for
        /// new submissions, if it was registered and open.
        closed_predecessor: Option<String>,
    },
    AlreadyRegistered,
}

/// Insert a verified challenge. Re-registering the identical definition is a no-op.
///
/// Supersession policy (docs/PROTOCOL_UPGRADES.md §2 step 6): registering a
/// challenge whose `supersedes` names a registered challenge closes that
/// predecessor for new submissions in the same transaction (grace period 0:
/// governance publishes the successor only once the grace period it
/// announced is over). A challenge registered *after* its successor (e.g. a
/// historical one loaded later from `ARENA_CHALLENGES_DIR`) is inserted closed.
/// Nothing else about the predecessor changes: its definition, submissions,
/// runs, reports and board are untouched.
pub async fn register(
    conn: &mut sqlx::PgConnection,
    v: &VerifiedChallenge,
    registered_by: &str,
) -> Result<RegisterOutcome, DbError> {
    let res = sqlx::query(
        "INSERT INTO challenges (id, digest, name, tier, definition, canonical_bytes, signature, governance_key, registered_by, open)
         VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9,
                 NOT EXISTS (SELECT 1 FROM challenges s WHERE s.definition->>'supersedes' = $1))
         ON CONFLICT (id) DO NOTHING",
    )
    .bind(&v.id)
    .bind(v.digest.as_str())
    .bind(&v.definition.name)
    .bind(crate::enum_str(&v.definition.tier))
    .bind(crate::json(&v.definition))
    .bind(&v.canonical_bytes)
    .bind(v.signature.to_bytes().to_vec())
    .bind(v.signer.to_bytes().to_vec())
    .bind(registered_by)
    .execute(&mut *conn)
    .await?;
    if res.rows_affected() != 1 {
        return Ok(RegisterOutcome::AlreadyRegistered);
    }
    let mut closed_predecessor = None;
    if let Some(prev) = &v.definition.supersedes {
        let n = sqlx::query("UPDATE challenges SET open = false WHERE id = $1 AND open")
            .bind(prev)
            .execute(&mut *conn)
            .await?
            .rows_affected();
        if n == 1 {
            closed_predecessor = Some(prev.clone());
        }
    }
    Ok(RegisterOutcome::Created { closed_predecessor })
}

/// Id of a registered successor of `id`, if any.
pub async fn successor_of<'e>(
    ex: impl PgExecutor<'e>,
    id: &str,
) -> Result<Option<String>, DbError> {
    let row: Option<(String,)> = sqlx::query_as(
        "SELECT id FROM challenges WHERE definition->>'supersedes' = $1 ORDER BY created_at, id LIMIT 1",
    )
    .bind(id)
    .fetch_optional(ex)
    .await?;
    Ok(row.map(|r| r.0))
}
