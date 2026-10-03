//! Admin endpoints (`/v1/admin/...`), authenticated with admin tokens
//! (separate table) and served from the admin DB pool.

use crate::api_types::*;
use crate::auth::AdminAuth;
use crate::error::{ApiError, ApiResult};
use crate::public::valid_id;
use crate::SharedState;
use arena_db::audit::AuditEvent;
use arena_db::challenge::{self, RegisterOutcome};
use arena_db::{audit, sqlx, tier_rank, Actor};
use arena_jobs::sanitize::{sanitize_line, MAX_REASON_BYTES};
use arena_types::challenge::Tier;
use arena_types::Revocation;
use axum::extract::{DefaultBodyLimit, Path, Query, State};
use axum::http::StatusCode;
use axum::routing::{get, post, put};
use axum::{Json, Router};
use serde_json::json;

pub fn routes(st: &SharedState) -> Router<SharedState> {
    Router::new()
        .route("/v1/admin/challenges", post(register_challenge))
        .route("/v1/admin/challenges/{id}/status", post(challenge_status))
        .route("/v1/admin/submissions/{id}/revoke", post(revoke))
        .route("/v1/admin/submissions/{id}/rerun", post(rerun))
        .route("/v1/admin/formal-cache/invalidate", post(invalidate_cache))
        .route("/v1/admin/agents", post(create_agent))
        .route("/v1/admin/workers", post(create_worker))
        .route("/v1/admin/quotas/{agent}", put(set_quota))
        .route("/v1/admin/audit", get(audit_log))
        .layer(DefaultBodyLimit::max(st.limits.max_json_bytes))
}

fn reason(r: &str) -> ApiResult<String> {
    let r = sanitize_line(r, MAX_REASON_BYTES);
    if r.is_empty() {
        return Err(ApiError::bad_request("a non-empty reason is required"));
    }
    Ok(r)
}

/// Register a challenge: the definition's ed25519 signature over its JCS bytes
/// must verify under a configured governance key; id and digest are recomputed.
async fn register_challenge(
    State(st): State<SharedState>,
    AdminAuth(admin): AdminAuth,
    Json(req): Json<RegisterChallengeRequest>,
) -> ApiResult<(StatusCode, Json<RegisterChallengeResponse>)> {
    let sig = challenge::parse_signature(&req.signature).map_err(ApiError::bad_request)?;
    let v = challenge::verify_definition(req.definition, &sig, st.orch.governance_keys())
        .map_err(|e| ApiError::new(StatusCode::BAD_REQUEST, "challenge_rejected", e))?;
    let mut tx = st.admin_db.begin().await?;
    let outcome = challenge::register(&mut *tx, &v, &format!("admin:{}", admin.id)).await?;
    let created = matches!(outcome, RegisterOutcome::Created);
    if created {
        audit::record(
            &mut *tx,
            &Actor::admin(&admin.id),
            "challenge.registered",
            None,
            None,
            true,
            json!({"challenge_id": v.id, "digest": v.digest, "governance_key": hex::encode(v.signer.to_bytes())}),
        )
        .await?;
    }
    tx.commit().await?;
    let status = if created {
        StatusCode::CREATED
    } else {
        StatusCode::OK
    };
    Ok((
        status,
        Json(RegisterChallengeResponse {
            id: v.id,
            digest: v.digest,
            created,
        }),
    ))
}

async fn challenge_status(
    State(st): State<SharedState>,
    AdminAuth(admin): AdminAuth,
    Path(id): Path<String>,
    Json(req): Json<ChallengeStatusRequest>,
) -> ApiResult<StatusCode> {
    let mut tx = st.admin_db.begin().await?;
    let n = sqlx::query("UPDATE challenges SET open = $2 WHERE id = $1")
        .bind(&id)
        .bind(req.open)
        .execute(&mut *tx)
        .await?
        .rows_affected();
    if n == 0 {
        return Err(ApiError::not_found("unknown challenge"));
    }
    audit::record(
        &mut *tx,
        &Actor::admin(&admin.id),
        "challenge.status",
        None,
        None,
        true,
        json!({"challenge_id": id, "open": req.open}),
    )
    .await?;
    tx.commit().await?;
    Ok(StatusCode::NO_CONTENT)
}

/// Revoke a submission's score. History (runs, gates, reports) is preserved;
/// the revocation is shown with its reason and the entry is never ranked.
async fn revoke(
    State(st): State<SharedState>,
    AdminAuth(admin): AdminAuth,
    Path(id): Path<String>,
    Json(req): Json<ReasonRequest>,
) -> ApiResult<(StatusCode, Json<Revocation>)> {
    let why = reason(&req.reason)?;
    if !valid_id("sub", &id)
        || arena_db::views::submission(&st.admin_db, &id)
            .await?
            .is_none()
    {
        return Err(ApiError::not_found("unknown submission"));
    }
    let mut tx = st.admin_db.begin().await?;
    let row: Option<(time::OffsetDateTime,)> = sqlx::query_as(
        "INSERT INTO revocations (submission_id, reason, revoked_by) VALUES ($1, $2, $3)
         ON CONFLICT (submission_id) DO NOTHING RETURNING revoked_at",
    )
    .bind(&id)
    .bind(&why)
    .bind(&admin.name)
    .fetch_optional(&mut *tx)
    .await?;
    let Some((at,)) = row else {
        return Err(ApiError::conflict(
            "already_revoked",
            "submission is already revoked",
        ));
    };
    audit::record(
        &mut *tx,
        &Actor::admin(&admin.id),
        "submission.revoked",
        Some(&id),
        None,
        true,
        json!({"reason": why}),
    )
    .await?;
    tx.commit().await?;
    Ok((
        StatusCode::CREATED,
        Json(Revocation {
            reason: why,
            revoked_at: arena_db::rfc3339(at),
            revoked_by: admin.name,
        }),
    ))
}

async fn rerun(
    State(st): State<SharedState>,
    AdminAuth(admin): AdminAuth,
    Path(id): Path<String>,
    Json(req): Json<ReasonRequest>,
) -> ApiResult<(StatusCode, Json<RerunResponse>)> {
    let why = reason(&req.reason)?;
    if !valid_id("sub", &id) {
        return Err(ApiError::not_found("unknown submission"));
    }
    let run_id = st
        .orch
        .rerun(&st.admin_db, &id, &Actor::admin(&admin.id), &why)
        .await?;
    Ok((
        StatusCode::CREATED,
        Json(RerunResponse {
            submission_id: id,
            run_id,
        }),
    ))
}

async fn invalidate_cache(
    State(st): State<SharedState>,
    AdminAuth(admin): AdminAuth,
    Json(req): Json<InvalidateCacheRequest>,
) -> ApiResult<Json<InvalidateCacheResponse>> {
    let why = reason(&req.reason)?;
    if req.checker_image.is_none() && req.assumption.is_none() {
        return Err(ApiError::bad_request(
            "specify checker_image and/or assumption",
        ));
    }
    let assumption = req.assumption.as_deref().map(|a| sanitize_line(a, 128));
    let mut tx = st.admin_db.begin().await?;
    let keys = arena_orchestrator::cache::invalidate(
        &mut tx,
        req.checker_image.as_ref().map(|d| d.as_str()),
        assumption.as_deref(),
        &admin.name,
        &why,
    )
    .await?;
    audit::record(
        &mut *tx,
        &Actor::admin(&admin.id),
        "formal_cache.invalidated",
        None,
        None,
        true,
        json!({"checker_image": req.checker_image, "assumption": assumption, "reason": why, "keys": keys}),
    )
    .await?;
    tx.commit().await?;
    Ok(Json(InvalidateCacheResponse { invalidated: keys }))
}

async fn create_agent(
    State(st): State<SharedState>,
    AdminAuth(admin): AdminAuth,
    Json(req): Json<CreateAgentRequest>,
) -> ApiResult<(StatusCode, Json<CreatedPrincipal>)> {
    let (id, token) = arena_db::create_agent(&st.admin_db, &req.handle)
        .await
        .map_err(db_create_err)?;
    audit::record(
        &st.admin_db,
        &Actor::admin(&admin.id),
        "agent.created",
        None,
        None,
        false,
        json!({"agent_id": id, "handle": req.handle}),
    )
    .await?;
    Ok((
        StatusCode::CREATED,
        Json(CreatedPrincipal {
            id,
            name: req.handle,
            token,
        }),
    ))
}

async fn create_worker(
    State(st): State<SharedState>,
    AdminAuth(admin): AdminAuth,
    Json(req): Json<CreateWorkerRequest>,
) -> ApiResult<(StatusCode, Json<CreatedPrincipal>)> {
    // The namespaces-only dev sandbox can never be leased non-demo work.
    let cap = if req.sandbox_backend == "bwrap-dev" {
        Tier::Demo
    } else {
        req.tier_cap
    };
    let (id, token) = arena_db::create_worker(&st.admin_db, &req.name, &req.sandbox_backend, cap)
        .await
        .map_err(db_create_err)?;
    audit::record(
        &st.admin_db,
        &Actor::admin(&admin.id),
        "worker.created",
        None,
        None,
        false,
        json!({"worker_id": id, "name": req.name, "sandbox_backend": req.sandbox_backend, "tier_cap": tier_rank(cap)}),
    )
    .await?;
    Ok((
        StatusCode::CREATED,
        Json(CreatedPrincipal {
            id,
            name: req.name,
            token,
        }),
    ))
}

fn db_create_err(e: arena_db::DbError) -> ApiError {
    match e {
        arena_db::DbError::Sqlx(s) => s.into(),
        e => e.into(),
    }
}

async fn set_quota(
    State(st): State<SharedState>,
    AdminAuth(admin): AdminAuth,
    Path(agent): Path<String>,
    Json(q): Json<QuotaRequest>,
) -> ApiResult<StatusCode> {
    let row: Option<(String,)> = sqlx::query_as("SELECT id FROM agents WHERE handle = $1")
        .bind(&agent)
        .fetch_optional(&st.admin_db)
        .await?;
    let (agent_id,) = row.ok_or_else(|| ApiError::not_found("unknown agent"))?;
    let mut tx = st.admin_db.begin().await?;
    sqlx::query(
        "INSERT INTO quotas (agent_id, max_submissions_per_day, max_upload_bytes_per_day, max_active_runs)
         VALUES ($1, $2, $3, $4)
         ON CONFLICT (agent_id) DO UPDATE SET max_submissions_per_day = EXCLUDED.max_submissions_per_day,
            max_upload_bytes_per_day = EXCLUDED.max_upload_bytes_per_day,
            max_active_runs = EXCLUDED.max_active_runs, updated_at = now()",
    )
    .bind(&agent_id)
    .bind(q.max_submissions_per_day)
    .bind(q.max_upload_bytes_per_day)
    .bind(q.max_active_runs)
    .execute(&mut *tx)
    .await?;
    audit::record(
        &mut *tx,
        &Actor::admin(&admin.id),
        "quota.set",
        None,
        None,
        false,
        json!({"agent_id": agent_id, "quota": q}),
    )
    .await?;
    tx.commit().await?;
    Ok(StatusCode::NO_CONTENT)
}

/// Full audit log (including non-public events), oldest first.
async fn audit_log(
    State(st): State<SharedState>,
    AdminAuth(_admin): AdminAuth,
    Query(q): Query<AuditQuery>,
) -> ApiResult<Json<Vec<AuditEvent>>> {
    let rows: Vec<AuditEvent> = sqlx::query_as(
        "SELECT id, at, actor_kind, actor_id, action, submission_id, run_id, public, data FROM audit_events
         WHERE ($1::text IS NULL OR submission_id = $1) AND id > $2 ORDER BY id LIMIT $3",
    )
    .bind(&q.submission_id)
    .bind(q.after.unwrap_or(0))
    .bind(q.limit.unwrap_or(500).clamp(1, 5000))
    .fetch_all(&st.admin_db)
    .await?;
    Ok(Json(rows))
}
