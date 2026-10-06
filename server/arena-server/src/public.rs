//! Public and agent endpoints (CONTRACTS §10).

use crate::api_types::*;
use crate::auth::AgentAuth;
use crate::error::{ApiError, ApiResult};
use crate::SharedState;
use arena_db::challenge::StoredChallenge;
use arena_db::views::{self, SubmissionFilter};
use arena_db::{audit, sqlx, Actor};
use arena_orchestrator::report::SignedReport;
use arena_types::{ChallengeDefinition, LeaderboardEntry, SubmissionView};
use axum::body::Body;
use axum::extract::{DefaultBodyLimit, Path, Query, State};
use axum::http::{HeaderMap, StatusCode};
use axum::response::sse::{Event, KeepAlive, Sse};
use axum::response::IntoResponse;
use axum::routing::{get, post};
use axum::{Json, Router};
use futures::StreamExt;
use serde_json::json;
use std::collections::{HashMap, VecDeque};
use std::convert::Infallible;
use std::time::Instant;

pub fn routes(st: &SharedState) -> Router<SharedState> {
    let json_limit = DefaultBodyLimit::max(st.limits.max_json_bytes);
    Router::new()
        .route("/healthz", get(healthz))
        .route("/v1/openapi.json", get(openapi))
        .route("/v1/challenges", get(list_challenges))
        .route("/v1/challenges/{id}", get(get_challenge))
        .route(
            "/v1/uploads",
            post(upload).layer(DefaultBodyLimit::disable()),
        )
        .route(
            "/v1/submissions",
            post(submit).get(list_submissions).layer(json_limit),
        )
        .route("/v1/submissions/{id}", get(get_submission))
        .route("/v1/submissions/{id}/events", get(events))
        .route("/v1/submissions/{id}/report", get(get_report))
        .route("/v1/submissions/{id}/cancel", post(cancel))
        .route("/v1/leaderboards/{challenge_id}", get(leaderboard))
}

async fn healthz(State(st): State<SharedState>) -> ApiResult<Json<serde_json::Value>> {
    sqlx::query("SELECT 1").execute(&st.api_db).await?;
    Ok(Json(json!({"ok": true, "dev": st.dev})))
}

async fn openapi() -> Json<serde_json::Value> {
    Json(crate::openapi::document())
}

pub(crate) fn valid_id(prefix: &str, s: &str) -> bool {
    s.len() == prefix.len() + 1 + 32
        && s.starts_with(prefix)
        && s.as_bytes()[prefix.len()] == b'_'
        && s[prefix.len() + 1..]
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

async fn list_challenges(State(st): State<SharedState>) -> ApiResult<Json<Vec<StoredChallenge>>> {
    Ok(Json(
        arena_db::challenge::list(&st.api_db, st.orch.governance_keys()).await?,
    ))
}

async fn load_challenge(st: &SharedState, id: &str) -> ApiResult<StoredChallenge> {
    if !valid_id("chl", id) {
        return Err(ApiError::not_found("unknown challenge"));
    }
    arena_db::challenge::load(&st.api_db, id, st.orch.governance_keys())
        .await?
        .ok_or_else(|| ApiError::not_found("unknown challenge"))
}

async fn get_challenge(
    State(st): State<SharedState>,
    Path(id): Path<String>,
) -> ApiResult<Json<StoredChallenge>> {
    Ok(Json(load_challenge(&st, &id).await?))
}

// ------------------------------------------------------------------ uploads

struct Quota {
    submissions_per_day: i64,
    upload_bytes_per_day: i64,
    active_runs: i64,
}

async fn quota_for(st: &SharedState, agent_id: &str) -> ApiResult<Quota> {
    let row: Option<(i32, i64, i32)> = sqlx::query_as(
        "SELECT max_submissions_per_day, max_upload_bytes_per_day, max_active_runs FROM quotas WHERE agent_id = $1",
    )
    .bind(agent_id)
    .fetch_optional(&st.api_db)
    .await?;
    Ok(match row {
        Some((s, b, a)) => Quota {
            submissions_per_day: s as i64,
            upload_bytes_per_day: b,
            active_runs: a as i64,
        },
        None => Quota {
            submissions_per_day: st.limits.submissions_per_day,
            upload_bytes_per_day: st.limits.upload_bytes_per_day,
            active_runs: st.limits.active_runs,
        },
    })
}

async fn upload(
    State(st): State<SharedState>,
    AgentAuth(agent): AgentAuth,
    headers: HeaderMap,
    body: Body,
) -> ApiResult<(StatusCode, Json<UploadResponse>)> {
    let quota = quota_for(&st, &agent.id).await?;
    let (used,): (i64,) = sqlx::query_as(
        "SELECT COALESCE(SUM(size_bytes), 0)::bigint FROM uploads WHERE agent_id = $1 AND created_at > now() - interval '1 day'",
    )
    .bind(&agent.id)
    .fetch_one(&st.api_db)
    .await?;
    let remaining = (quota.upload_bytes_per_day - used).max(0) as u64;
    if remaining == 0 {
        return Err(ApiError::too_many(
            "quota_exceeded",
            "daily upload byte quota exhausted",
            3600,
        ));
    }
    let limit = st.limits.max_upload_bytes.min(remaining);
    let quota_bound = limit < st.limits.max_upload_bytes;
    let over = |_: ()| {
        if quota_bound {
            ApiError::too_many(
                "quota_exceeded",
                "upload exceeds the remaining daily upload quota",
                3600,
            )
        } else {
            ApiError::new(
                StatusCode::PAYLOAD_TOO_LARGE,
                "too_large",
                format!(
                    "package exceeds the {}-byte limit",
                    st.limits.max_upload_bytes
                ),
            )
        }
    };
    if let Some(len) = headers
        .get(axum::http::header::CONTENT_LENGTH)
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.parse::<u64>().ok())
    {
        if len > limit {
            return Err(over(()));
        }
    }
    let mut w = st.store.writer(limit).await?;
    let mut stream = body.into_data_stream();
    while let Some(chunk) = stream.next().await {
        let chunk = chunk.map_err(|e| ApiError::bad_request(format!("body: {e}")))?;
        match w.write(&chunk).await {
            Ok(()) => {}
            Err(arena_store::StoreError::TooLarge { .. }) => return Err(over(())),
            Err(e) => return Err(e.into()),
        }
    }
    let out = w.finish(None).await?;
    if out.size == 0 {
        return Err(ApiError::bad_request("empty upload"));
    }
    let id = arena_db::new_id("upl");
    let mut tx = st.api_db.begin().await?;
    // Re-check the daily byte quota under the agent row lock: the check above
    // runs before streaming and is not serialized, so concurrent uploads could
    // each consume the full remaining quota (red-team RT-06).
    sqlx::query("SELECT id FROM agents WHERE id = $1 FOR UPDATE")
        .bind(&agent.id)
        .execute(&mut *tx)
        .await?;
    let (used_now, already): (i64, bool) = sqlx::query_as(
        "SELECT (SELECT COALESCE(SUM(size_bytes), 0)::bigint FROM uploads
                 WHERE agent_id = $1 AND created_at > now() - interval '1 day'),
                EXISTS (SELECT 1 FROM uploads WHERE agent_id = $1 AND digest = $2)",
    )
    .bind(&agent.id)
    .bind(out.digest.as_str())
    .fetch_one(&mut *tx)
    .await?;
    if !already && used_now.saturating_add(out.size as i64) > quota.upload_bytes_per_day {
        return Err(ApiError::too_many(
            "quota_exceeded",
            "upload exceeds the remaining daily upload quota",
            3600,
        ));
    }
    sqlx::query(
        "INSERT INTO uploads (id, agent_id, digest, size_bytes) VALUES ($1, $2, $3, $4)
         ON CONFLICT (agent_id, digest) DO NOTHING",
    )
    .bind(&id)
    .bind(&agent.id)
    .bind(out.digest.as_str())
    .bind(out.size as i64)
    .execute(&mut *tx)
    .await?;
    let (upload_id,): (String,) =
        sqlx::query_as("SELECT id FROM uploads WHERE agent_id = $1 AND digest = $2")
            .bind(&agent.id)
            .bind(out.digest.as_str())
            .fetch_one(&mut *tx)
            .await?;
    audit::record(
        &mut *tx,
        &Actor::agent(&agent.id),
        "upload.created",
        None,
        None,
        false,
        json!({"upload_id": upload_id, "digest": out.digest, "size_bytes": out.size}),
    )
    .await?;
    tx.commit().await?;
    Ok((
        StatusCode::CREATED,
        Json(UploadResponse {
            upload_id,
            digest: out.digest,
            size_bytes: out.size,
        }),
    ))
}

// ------------------------------------------------------------------ submissions

fn idempotency_key_ok(k: &str) -> bool {
    !k.is_empty()
        && k.len() <= 128
        && k.bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b':' | b'-'))
}

async fn view_of(st: &SharedState, id: &str) -> ApiResult<SubmissionView> {
    let b = views::bundle(&st.api_db, id)
        .await?
        .ok_or_else(|| ApiError::not_found("unknown submission"))?;
    let chal = load_challenge(st, &b.sub.challenge_id).await?;
    Ok(b.view(&chal.definition))
}

async fn submit(
    State(st): State<SharedState>,
    AgentAuth(agent): AgentAuth,
    Json(req): Json<SubmitRequest>,
) -> ApiResult<(StatusCode, Json<SubmissionView>)> {
    if !idempotency_key_ok(&req.idempotency_key) {
        return Err(ApiError::bad_request(
            "idempotency_key must match [A-Za-z0-9._:-]{1,128}",
        ));
    }
    let request_digest = arena_types::sha256_digest(&json!({
        "challenge_id": req.challenge_id, "upload_digest": req.upload_digest, "parent": req.parent,
    }))
    .map_err(ApiError::internal)?;
    let mut tx = st.api_db.begin().await?;
    // Serializes this agent's submissions: idempotency and quota checks are exact.
    sqlx::query("SELECT id FROM agents WHERE id = $1 FOR UPDATE")
        .bind(&agent.id)
        .execute(&mut *tx)
        .await?;
    let existing: Option<(String, String)> = sqlx::query_as(
        "SELECT id, request_digest FROM submissions WHERE agent_id = $1 AND idempotency_key = $2",
    )
    .bind(&agent.id)
    .bind(&req.idempotency_key)
    .fetch_optional(&mut *tx)
    .await?;
    if let Some((id, digest)) = existing {
        drop(tx);
        if digest != request_digest.as_str() {
            return Err(ApiError::conflict(
                "idempotency_conflict",
                "idempotency_key was already used with a different request body",
            ));
        }
        return Ok((StatusCode::OK, Json(view_of(&st, &id).await?)));
    }
    let chal = load_challenge(&st, &req.challenge_id).await?;
    if !chal.open {
        return Err(ApiError::conflict(
            "challenge_closed",
            match &chal.superseded_by {
                Some(succ) => format!(
                    "challenge is superseded by {succ} and closed for new submissions; submit against {succ}"
                ),
                None => "challenge is not accepting submissions".to_string(),
            },
        ));
    }
    let upload: Option<(String,)> =
        sqlx::query_as("SELECT id FROM uploads WHERE agent_id = $1 AND digest = $2")
            .bind(&agent.id)
            .bind(req.upload_digest.as_str())
            .fetch_optional(&mut *tx)
            .await?;
    let (upload_id,) = upload.ok_or_else(|| {
        ApiError::bad_request("upload_digest does not refer to one of your uploads")
    })?;
    if !st.store.exists(&req.upload_digest).await? {
        return Err(ApiError::internal(format!(
            "uploaded object {} missing from store",
            req.upload_digest
        )));
    }
    if let Some(p) = &req.parent {
        let parent: Option<(String,)> =
            sqlx::query_as("SELECT challenge_id FROM submissions WHERE id = $1")
                .bind(p)
                .fetch_optional(&mut *tx)
                .await?;
        match parent {
            None => return Err(ApiError::bad_request("parent submission does not exist")),
            Some((c,)) if c != chal.id => {
                return Err(ApiError::bad_request(
                    "parent submission belongs to a different challenge",
                ))
            }
            Some(_) => {}
        }
    }
    let quota = quota_for(&st, &agent.id).await?;
    let (recent,): (i64,) = sqlx::query_as(
        "SELECT count(*) FROM submissions WHERE agent_id = $1 AND created_at > now() - interval '1 day'",
    )
    .bind(&agent.id)
    .fetch_one(&mut *tx)
    .await?;
    if recent >= quota.submissions_per_day {
        return Err(ApiError::too_many(
            "quota_exceeded",
            "daily submission quota exhausted",
            3600,
        ));
    }
    let (active,): (i64,) = sqlx::query_as(
        "SELECT count(*) FROM runs r JOIN submissions s ON s.id = r.submission_id
         WHERE s.agent_id = $1 AND r.decision IS NULL",
    )
    .bind(&agent.id)
    .fetch_one(&mut *tx)
    .await?;
    if active >= quota.active_runs {
        return Err(ApiError::too_many(
            "quota_exceeded",
            "too many submissions in progress",
            60,
        ));
    }
    let id = arena_db::new_id("sub");
    sqlx::query(
        "INSERT INTO submissions (id, agent_id, challenge_id, package_digest, upload_id, parent_id, idempotency_key, request_digest)
         VALUES ($1, $2, $3, $4, $5, $6, $7, $8)",
    )
    .bind(&id)
    .bind(&agent.id)
    .bind(&chal.id)
    .bind(req.upload_digest.as_str())
    .bind(&upload_id)
    .bind(&req.parent)
    .bind(&req.idempotency_key)
    .bind(request_digest.as_str())
    .execute(&mut *tx)
    .await?;
    let actor = Actor::agent(&agent.id);
    audit::record(
        &mut *tx,
        &actor,
        "submission.created",
        Some(&id),
        None,
        true,
        json!({"challenge_id": chal.id, "package_digest": req.upload_digest, "parent": req.parent}),
    )
    .await?;
    st.orch.start_run(&mut tx, &id, "submit", &actor).await?;
    tx.commit().await?;
    Ok((StatusCode::CREATED, Json(view_of(&st, &id).await?)))
}

async fn list_submissions(
    State(st): State<SharedState>,
    Query(q): Query<SubmissionsQuery>,
) -> ApiResult<Json<Vec<SubmissionView>>> {
    let f = SubmissionFilter {
        challenge_id: q.challenge_id,
        agent_handle: q.agent,
        limit: q.limit.unwrap_or(100).clamp(1, 500),
        before_id: q.before,
    };
    let bundles = views::list_bundles(&st.api_db, &f).await?;
    let mut defs: HashMap<String, ChallengeDefinition> = HashMap::new();
    let mut out = Vec::with_capacity(bundles.len());
    for b in &bundles {
        if !defs.contains_key(&b.sub.challenge_id) {
            let c = load_challenge(&st, &b.sub.challenge_id).await?;
            defs.insert(c.id.clone(), c.definition);
        }
        out.push(b.view(&defs[&b.sub.challenge_id]));
    }
    Ok(Json(out))
}

async fn get_submission(
    State(st): State<SharedState>,
    Path(id): Path<String>,
) -> ApiResult<Json<SubmissionView>> {
    if !valid_id("sub", &id) {
        return Err(ApiError::not_found("unknown submission"));
    }
    Ok(Json(view_of(&st, &id).await?))
}

async fn get_report(
    State(st): State<SharedState>,
    Path(id): Path<String>,
) -> ApiResult<Json<SignedReport>> {
    if !valid_id("sub", &id) || views::submission(&st.api_db, &id).await?.is_none() {
        return Err(ApiError::not_found("unknown submission"));
    }
    match arena_orchestrator::report::load_latest(&st.api_db, &id).await? {
        Some(r) => Ok(Json(r)),
        None => Err(ApiError::conflict(
            "pending",
            "no decided run yet; the report is issued at decision time",
        )),
    }
}

async fn cancel(
    State(st): State<SharedState>,
    AgentAuth(agent): AgentAuth,
    Path(id): Path<String>,
) -> ApiResult<Json<SubmissionView>> {
    let sub = views::submission(&st.api_db, &id)
        .await?
        .ok_or_else(|| ApiError::not_found("unknown submission"))?;
    if sub.agent_id != agent.id {
        return Err(ApiError::forbidden("only the submitting agent can cancel"));
    }
    st.orch
        .cancel(&st.api_db, &id, &Actor::agent(&agent.id))
        .await
        .map_err(|e| match e {
            arena_orchestrator::OrchError::Conflict(m) => ApiError::conflict("already_decided", m),
            e => e.into(),
        })?;
    Ok(Json(view_of(&st, &id).await?))
}

#[derive(serde::Deserialize, Default)]
struct BoardQuery {
    /// `speed` (default) or `cost_v1`.
    board: Option<arena_types::ScoringKind>,
}

async fn leaderboard(
    State(st): State<SharedState>,
    Path(challenge_id): Path<String>,
    Query(q): Query<BoardQuery>,
) -> ApiResult<Json<Vec<LeaderboardEntry>>> {
    let chal = load_challenge(&st, &challenge_id).await?;
    let f = SubmissionFilter {
        challenge_id: Some(chal.id.clone()),
        limit: 10_000,
        ..Default::default()
    };
    let bundles = views::list_bundles(&st.api_db, &f).await?;
    let board = q.board.unwrap_or(arena_types::ScoringKind::Speed);
    views::compute_leaderboard(
        &chal.id,
        &chal.definition,
        chal.superseded_by.as_deref(),
        &bundles,
    )
    .entries_for(board)
    .map(Json)
    .ok_or_else(|| {
        ApiError::not_found("this challenge has no cost board (no scoring.kind = cost_v1)")
    })
}

// ------------------------------------------------------------------ SSE

struct SseState {
    st: SharedState,
    sub: String,
    last: i64,
    buf: VecDeque<arena_db::audit::AuditEvent>,
    started: Instant,
    finished: bool,
}

/// Public pipeline events of a submission, backed by the append-only audit
/// log (polled). Resumable with `Last-Event-ID` or `?after=`. The stream ends
/// once the latest run is decided and all its events were delivered.
async fn events(
    State(st): State<SharedState>,
    Path(id): Path<String>,
    Query(q): Query<EventsQuery>,
    headers: HeaderMap,
) -> ApiResult<impl IntoResponse> {
    if !valid_id("sub", &id) || views::submission(&st.api_db, &id).await?.is_none() {
        return Err(ApiError::not_found("unknown submission"));
    }
    let last = headers
        .get("last-event-id")
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.parse::<i64>().ok())
        .or(q.after)
        .unwrap_or(0);
    let init = SseState {
        st,
        sub: id,
        last,
        buf: VecDeque::new(),
        started: Instant::now(),
        finished: false,
    };
    let stream = futures::stream::unfold(init, |mut s| async move {
        loop {
            if let Some(e) = s.buf.pop_front() {
                s.last = e.id;
                let kind = match e.action.as_str() {
                    "run.stage" => "stage",
                    "gate.result" => "gate",
                    "run.decided" => "decision",
                    "job.failed" => "log",
                    _ => "progress",
                };
                let payload = EventPayload {
                    id: e.id,
                    at: arena_db::rfc3339(e.at),
                    action: e.action,
                    run_id: e.run_id,
                    data: e.data,
                };
                let ev = Event::default()
                    .id(e.id.to_string())
                    .event(kind)
                    .data(serde_json::to_string(&payload).unwrap_or_default());
                return Some((Ok::<_, Infallible>(ev), s));
            }
            if s.finished || s.started.elapsed() > s.st.limits.sse_max_duration {
                return None;
            }
            // Check "decided" BEFORE fetching so that no event committed with the
            // decision can be missed.
            let decided: Result<Option<(bool,)>, _> = sqlx::query_as(
                "SELECT decision IS NOT NULL FROM runs WHERE submission_id = $1 ORDER BY run_number DESC LIMIT 1",
            )
            .bind(&s.sub)
            .fetch_optional(&s.st.api_db)
            .await;
            let decided = matches!(decided, Ok(Some((true,))));
            match arena_db::audit::public_events_after(&s.st.api_db, &s.sub, s.last, 200).await {
                Ok(evs) if !evs.is_empty() => s.buf.extend(evs),
                Ok(_) if decided => {
                    s.finished = true;
                    let ev = Event::default().event("done").data("{}");
                    return Some((Ok(ev), s));
                }
                Ok(_) => tokio::time::sleep(s.st.limits.sse_poll).await,
                Err(e) => {
                    tracing::warn!("sse poll: {e}");
                    tokio::time::sleep(s.st.limits.sse_poll * 4).await;
                }
            }
        }
    });
    Ok(Sse::new(stream).keep_alive(KeepAlive::default()))
}
