//! Signed judge reports.
//!
//! A report is an attestation of what the judge did for one run: the exact
//! challenge and package digests, every gate result (including which were
//! reused from the formal cache and which were never run), the jobs that ran
//! and on which sandbox backend/tier, the artifacts produced, measurements and
//! the evidence graph. It is serialized as canonical JSON (JCS) and signed
//! with the control plane's ed25519 report key at decision time. Reports are
//! immutable; a rerun produces a new run and a new report. Revocations are
//! returned alongside (unsigned, they post-date the report).

use crate::signer::ReportSigner;
use crate::Ctx;
use arena_db::{rfc3339, views, DbError};
use arena_types::{canonical_json, challenge::Tier, EvidenceRef, Revocation};
use serde::Serialize;
use serde_json::{json as j, Value};
use sqlx::{PgConnection, PgExecutor};
use time::OffsetDateTime;

pub const REPORT_SCHEMA: &str = "arena-report-v1";

#[derive(sqlx::FromRow)]
struct JobInfo {
    kind: String,
    state: String,
    attempt: i32,
    max_attempts: i32,
    lease_owner: Option<String>,
    execution: Option<Value>,
    result: Option<Value>,
    last_error: Option<String>,
    created_at: OffsetDateTime,
    finished_at: Option<OffsetDateTime>,
}

fn disclaimers(tier: Tier, challenge_tier: Tier) -> Vec<&'static str> {
    let mut d = vec![
        "This report attests to the checks the arena judge executed; it does not establish \
         properties listed in the challenge's semantic_scope.excludes.",
    ];
    match tier {
        Tier::Demo => d.push(
            "DEMO tier: produced with simulated components and/or the bwrap-dev sandbox. \
             Not a formal admission and never ranked.",
        ),
        Tier::Experimental => {
            d.push("EXPERIMENTAL tier: tests and diagnostic timings only; never ranked as formal.")
        }
        Tier::Formal => {}
    }
    if tier != challenge_tier {
        d.push("Effective tier is lower than the challenge tier because part of the evaluation ran with a lower-assurance sandbox or worker.");
    }
    d
}

/// Build, sign and store the report for a just-decided run.
pub(crate) async fn build_and_store(
    conn: &mut PgConnection,
    ctx: &Ctx,
    signer: &ReportSigner,
) -> Result<(), DbError> {
    let run = arena_db::views::run(&mut *conn, &ctx.run.id)
        .await?
        .ok_or_else(|| DbError::corrupt("run vanished"))?;
    let gates = views::gates_of(&mut *conn, std::slice::from_ref(&run.id))
        .await?
        .remove(&run.id)
        .unwrap_or_default()
        .into_iter()
        .map(views::public_gate)
        .collect::<Vec<_>>();
    let jobs: Vec<JobInfo> = sqlx::query_as(
        "SELECT kind, state, attempt, max_attempts, lease_owner, execution, result, last_error, created_at, finished_at
         FROM jobs WHERE run_id = $1 ORDER BY created_at, kind",
    )
    .bind(&run.id)
    .fetch_all(&mut *conn)
    .await?;
    let mut artifacts: Vec<EvidenceRef> = Vec::new();
    let mut job_vals = Vec::new();
    for jb in &jobs {
        if let Some(arts) = jb.result.as_ref().and_then(|r| r.get("artifacts")) {
            if let Ok(list) = serde_json::from_value::<Vec<EvidenceRef>>(arts.clone()) {
                artifacts.extend(list.into_iter().filter(|a| a.public));
            }
        }
        job_vals.push(j!({
            "kind": jb.kind,
            "state": jb.state,
            "attempts": jb.attempt,
            "max_attempts": jb.max_attempts,
            "worker_id": jb.lease_owner,
            "execution": jb.execution,
            "last_error": jb.last_error,
            "enqueued_at": rfc3339(jb.created_at),
            "finished_at": jb.finished_at.map(rfc3339),
        }));
    }
    let reused_from = gates.iter().find_map(|g| g.reused_from.clone());
    let report = j!({
        "schema": REPORT_SCHEMA,
        "contracts": arena_types::SCHEMA_VERSION,
        "judge": {
            "server": concat!("arena-server/", env!("CARGO_PKG_VERSION")),
            "report_key": signer.public_key_hex(),
        },
        "issued_at": rfc3339(OffsetDateTime::now_utc()),
        "challenge": {
            "id": ctx.chal.id,
            "digest": ctx.chal.digest,
            "tier": ctx.chal.tier,
            "governance_key": ctx.chal.governance_key,
            "scope": ctx.chal.definition.semantic_scope.name,
            "excludes": ctx.chal.definition.semantic_scope.excludes,
            "security_profile": ctx.chal.definition.security_profile.id,
            "required_obligations": ctx.chal.definition.required_obligations,
        },
        "submission": {
            "id": ctx.sub.id,
            "agent": ctx.sub.agent_handle,
            "package_digest": ctx.sub.package_digest,
            "parent": ctx.sub.parent_id,
            "created_at": rfc3339(ctx.sub.created_at),
        },
        "run": {
            "id": run.id,
            "run_number": run.run_number,
            "trigger": run.trigger,
            "requested_by": run.requested_by,
            "challenge_tier": run.challenge_tier,
            "tier": run.tier,
            "stage": run.stage,
            "decision": run.decision,
            "accepted": run.accepted,
            "score_milli": run.score_milli,
            "change_class": run.change_class,
            "reason_codes": run.reason_codes,
            "not_run_gates": run.not_run_gates,
            "created_at": rfc3339(run.created_at),
            "decided_at": run.decided_at.map(rfc3339),
        },
        "candidate": {
            "name": run.candidate_name,
            "backend_family": run.backend_family,
            "manifest": run.manifest,
        },
        "verified_surface": run.verified_surface,
        "build_outputs": run.build_outputs,
        "formal_cache": { "key": run.formal_cache_key, "reused_from": reused_from },
        "gates": gates,
        "jobs": job_vals,
        "artifacts": artifacts,
        "benchmark": run.benchmark,
        "evidence_graph": run.evidence_graph,
        "disclaimers": disclaimers(run.tier, run.challenge_tier),
    });
    let bytes = canonical_json(&report).map_err(DbError::corrupt)?;
    let sig = signer.sign(&bytes);
    sqlx::query(
        "INSERT INTO reports (run_id, submission_id, canonical_bytes, signature, public_key) VALUES ($1, $2, $3, $4, $5)",
    )
    .bind(&run.id)
    .bind(&ctx.sub.id)
    .bind(&bytes)
    .bind(sig.to_vec())
    .bind(signer.verifying_key().to_bytes().to_vec())
    .execute(&mut *conn)
    .await?;
    Ok(())
}

/// API envelope for `GET /v1/submissions/{id}/report`.
#[derive(Clone, Debug, Serialize, serde::Deserialize, schemars::JsonSchema)]
pub struct SignedReport {
    pub algorithm: String,
    pub canonicalization: String,
    /// Hex ed25519 public key of the control plane's report key.
    pub public_key: String,
    /// Hex signature over the canonical (JCS) bytes of `report`.
    pub signature: String,
    pub report: Value,
    /// Revocation recorded after the report was issued (not covered by the signature).
    pub revocation: Option<Revocation>,
}

/// Latest signed report of a submission (latest decided run).
pub async fn load_latest<'e>(
    ex: impl PgExecutor<'e> + Copy,
    submission_id: &str,
) -> Result<Option<SignedReport>, DbError> {
    let row: Option<(Vec<u8>, Vec<u8>, Vec<u8>)> = sqlx::query_as(
        "SELECT rep.canonical_bytes, rep.signature, rep.public_key FROM reports rep
         JOIN runs r ON r.id = rep.run_id WHERE rep.submission_id = $1
         ORDER BY r.run_number DESC LIMIT 1",
    )
    .bind(submission_id)
    .fetch_optional(ex)
    .await?;
    let Some((bytes, sig, pk)) = row else {
        return Ok(None);
    };
    let revocation = views::revocations_of(ex, &[submission_id.to_string()])
        .await?
        .remove(submission_id);
    let report: Value = serde_json::from_slice(&bytes).map_err(DbError::corrupt)?;
    Ok(Some(SignedReport {
        algorithm: "ed25519".into(),
        canonicalization: "JCS (RFC 8785, integers only)".into(),
        public_key: hex::encode(pk),
        signature: hex::encode(sig),
        report,
        revocation,
    }))
}

/// Verify a signed report envelope (used by tests and clients).
pub fn verify(env: &SignedReport) -> Result<(), String> {
    use ed25519_dalek::{Signature, Verifier, VerifyingKey};
    let pk: [u8; 32] = hex::decode(&env.public_key)
        .map_err(|e| e.to_string())?
        .try_into()
        .map_err(|_| "pk len")?;
    let sig: [u8; 64] = hex::decode(&env.signature)
        .map_err(|e| e.to_string())?
        .try_into()
        .map_err(|_| "sig len")?;
    let bytes = canonical_json(&env.report).map_err(|e| e.to_string())?;
    VerifyingKey::from_bytes(&pk)
        .map_err(|e| e.to_string())?
        .verify(&bytes, &Signature::from_bytes(&sig))
        .map_err(|e| e.to_string())
}
