//! Content-addressed formal-result cache.
//!
//! Key = sha256(JCS{challenge digest, verified surface, checker image,
//! assumption set, axiom allowlist, rechecker set}). Because the key commits
//! to everything the formal gates depend on, a hit is sound regardless of
//! lineage. Entries are never deleted; invalidation (by checker image or by
//! assumption id) marks them dead and keeps them for history.

use arena_db::{from_json, from_json_opt, json, DbError};
use arena_types::{
    sha256_digest, ChallengeDefinition, Digest, EvidenceGraph, GateResult, VerifiedSurface,
};
use serde::Serialize;
use sqlx::PgConnection;

#[derive(Serialize)]
struct KeyMaterial<'a> {
    v: &'static str,
    challenge_digest: &'a Digest,
    verified_surface: &'a VerifiedSurface,
    checker_image: &'a Digest,
    assumptions: Vec<&'a str>,
    axiom_allowlist: Vec<&'a str>,
    recheckers: Vec<&'a str>,
    lean_toolchain: &'a str,
}

pub fn sorted_assumptions(chal: &ChallengeDefinition) -> Vec<String> {
    let mut a = chal.security_profile.allowed_assumptions.clone();
    a.sort();
    a.dedup();
    a
}

pub fn cache_key(chal_digest: &Digest, chal: &ChallengeDefinition, vs: &VerifiedSurface) -> Digest {
    fn sorted(v: &[String]) -> Vec<&str> {
        let mut x: Vec<&str> = v.iter().map(|s| s.as_str()).collect();
        x.sort();
        x.dedup();
        x
    }
    let km = KeyMaterial {
        v: "arena-formal-cache-v1",
        challenge_digest: chal_digest,
        verified_surface: vs,
        checker_image: &chal.toolchain_policy.checker_image,
        assumptions: sorted(&chal.security_profile.allowed_assumptions),
        axiom_allowlist: sorted(&chal.toolchain_policy.axiom_allowlist),
        recheckers: sorted(&chal.toolchain_policy.recheckers),
        lean_toolchain: &chal.toolchain_policy.lean_toolchain,
    };
    sha256_digest(&km).expect("cache key material has no floats")
}

#[derive(Clone, Debug)]
pub struct CacheEntry {
    pub id: i64,
    pub gates: Vec<GateResult>,
    pub evidence_graph: Option<EvidenceGraph>,
    pub source_submission_id: String,
    pub source_run_id: String,
    pub tier_rank: i16,
}

pub async fn lookup(conn: &mut PgConnection, key: &Digest) -> Result<Option<CacheEntry>, DbError> {
    let row: Option<(
        i64,
        serde_json::Value,
        Option<serde_json::Value>,
        String,
        String,
        i16,
    )> = sqlx::query_as(
        "SELECT id, gates, evidence_graph, source_submission_id, source_run_id, tier_rank
         FROM formal_cache WHERE key = $1 AND invalidated_at IS NULL",
    )
    .bind(key.as_str())
    .fetch_optional(&mut *conn)
    .await?;
    row.map(|(id, g, eg, s, r, t)| {
        Ok(CacheEntry {
            id,
            gates: from_json(g)?,
            evidence_graph: from_json_opt(eg)?,
            source_submission_id: s,
            source_run_id: r,
            tier_rank: t,
        })
    })
    .transpose()
}

#[allow(clippy::too_many_arguments)]
pub async fn store(
    conn: &mut PgConnection,
    key: &Digest,
    challenge_id: &str,
    chal_digest: &Digest,
    chal: &ChallengeDefinition,
    vs: &VerifiedSurface,
    gates: &[GateResult],
    evidence_graph: Option<&EvidenceGraph>,
    tier_rank: i16,
    submission_id: &str,
    run_id: &str,
) -> Result<bool, DbError> {
    let res = sqlx::query(
        "INSERT INTO formal_cache (key, challenge_id, challenge_digest, verified_surface, checker_image,
            assumptions, tier_rank, gates, evidence_graph, source_submission_id, source_run_id)
         VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11)
         ON CONFLICT (key) WHERE invalidated_at IS NULL DO NOTHING",
    )
    .bind(key.as_str())
    .bind(challenge_id)
    .bind(chal_digest.as_str())
    .bind(json(vs))
    .bind(chal.toolchain_policy.checker_image.as_str())
    .bind(sorted_assumptions(chal))
    .bind(tier_rank)
    .bind(json(&gates))
    .bind(evidence_graph.map(json))
    .bind(submission_id)
    .bind(run_id)
    .execute(&mut *conn)
    .await?;
    Ok(res.rows_affected() == 1)
}

/// Invalidate live entries matching a checker image and/or an assumption id.
/// Returns the invalidated keys.
pub async fn invalidate(
    conn: &mut PgConnection,
    checker_image: Option<&str>,
    assumption: Option<&str>,
    by: &str,
    reason: &str,
) -> Result<Vec<String>, DbError> {
    if checker_image.is_none() && assumption.is_none() {
        return Ok(vec![]);
    }
    let rows: Vec<(String,)> = sqlx::query_as(
        "UPDATE formal_cache SET invalidated_at = now(), invalidated_by = $3, invalidated_reason = $4
         WHERE invalidated_at IS NULL
           AND ($1::text IS NULL OR checker_image = $1)
           AND ($2::text IS NULL OR $2 = ANY(assumptions))
         RETURNING key",
    )
    .bind(checker_image)
    .bind(assumption)
    .bind(by)
    .bind(reason)
    .fetch_all(&mut *conn)
    .await?;
    Ok(rows.into_iter().map(|r| r.0).collect())
}
