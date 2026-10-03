//! Internal worker API (`/internal/v1/...`), served on its own listener.
//! Authenticated with worker tokens; backed by the worker-gateway DB pool.
//! Nothing reachable from here exposes the report signing key, admin data or
//! database credentials.

use crate::auth::WorkerAuth;
use crate::error::{ApiError, ApiResult};
use crate::SharedState;
use arena_db::sqlx;
use arena_jobs::*;
use arena_types::Digest;
use axum::body::Body;
use axum::extract::{DefaultBodyLimit, Path, State};
use axum::http::{header, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::routing::{get, post};
use axum::{Json, Router};
use futures::StreamExt;
use uuid::Uuid;

pub fn routes(st: &SharedState) -> Router<SharedState> {
    let json_limit = DefaultBodyLimit::max(st.limits.max_json_bytes * 16);
    Router::new()
        .route("/internal/v1/jobs/lease", post(lease).layer(json_limit))
        .route(
            "/internal/v1/jobs/{id}/heartbeat",
            post(heartbeat).layer(json_limit),
        )
        .route(
            "/internal/v1/jobs/{id}/complete",
            post(complete).layer(json_limit),
        )
        .route("/internal/v1/jobs/{id}/fail", post(fail).layer(json_limit))
        .route(
            "/internal/v1/artifacts/{digest}",
            get(get_artifact)
                .put(put_artifact)
                .layer(DefaultBodyLimit::disable()),
        )
}

fn job_id(s: &str) -> ApiResult<Uuid> {
    Uuid::parse_str(s).map_err(|_| ApiError::not_found("unknown job"))
}

fn digest(s: &str) -> ApiResult<Digest> {
    Digest::try_from(s.to_string())
        .map_err(|_| ApiError::bad_request("path must be a sha256:<hex> digest"))
}

async fn lease(
    State(st): State<SharedState>,
    WorkerAuth(w): WorkerAuth,
    body: Option<Json<LeaseRequest>>,
) -> ApiResult<Response> {
    let req = body.map(|b| b.0).unwrap_or_default();
    match st.orch.lease(&st.worker_db, &w, &req).await? {
        Some(job) => Ok(Json(job).into_response()),
        None => Ok(StatusCode::NO_CONTENT.into_response()),
    }
}

async fn heartbeat(
    State(st): State<SharedState>,
    WorkerAuth(w): WorkerAuth,
    Path(id): Path<String>,
    Json(req): Json<HeartbeatRequest>,
) -> ApiResult<Json<HeartbeatResponse>> {
    Ok(Json(
        st.orch
            .heartbeat(&st.worker_db, &w, job_id(&id)?, &req)
            .await?,
    ))
}

async fn complete(
    State(st): State<SharedState>,
    WorkerAuth(w): WorkerAuth,
    Path(id): Path<String>,
    Json(req): Json<CompleteRequest>,
) -> ApiResult<Json<AckResponse>> {
    // Every referenced artifact must already be in the store (upload first,
    // then complete). This does not consume an attempt.
    for d in req
        .result
        .artifacts
        .iter()
        .map(|a| &a.digest)
        .chain(req.result.native_verifier.iter())
    {
        if !st.store.exists(d).await? {
            return Err(ApiError::new(
                StatusCode::UNPROCESSABLE_ENTITY,
                "artifact_missing",
                format!("artifact {d} was not uploaded"),
            ));
        }
    }
    Ok(Json(
        st.orch
            .complete(&st.worker_db, &w, job_id(&id)?, &req)
            .await?,
    ))
}

async fn fail(
    State(st): State<SharedState>,
    WorkerAuth(w): WorkerAuth,
    Path(id): Path<String>,
    Json(req): Json<FailRequest>,
) -> ApiResult<Json<AckResponse>> {
    Ok(Json(
        st.orch.fail(&st.worker_db, &w, job_id(&id)?, &req).await?,
    ))
}

async fn get_artifact(
    State(st): State<SharedState>,
    WorkerAuth(_w): WorkerAuth,
    Path(d): Path<String>,
) -> ApiResult<Response> {
    let d = digest(&d)?;
    let Some(obj) = st.store.open(&d).await? else {
        return Err(ApiError::not_found("unknown artifact"));
    };
    let stream = tokio_util::io::ReaderStream::with_capacity(obj.reader, 64 * 1024);
    Ok((
        [
            (header::CONTENT_TYPE, "application/octet-stream".to_string()),
            (header::CONTENT_LENGTH, obj.size.to_string()),
        ],
        Body::from_stream(stream),
    )
        .into_response())
}

async fn put_artifact(
    State(st): State<SharedState>,
    WorkerAuth(w): WorkerAuth,
    Path(d): Path<String>,
    body: Body,
) -> ApiResult<(StatusCode, Json<ArtifactPutResponse>)> {
    let expected = digest(&d)?;
    let mut wr = st.store.writer(st.limits.max_artifact_bytes).await?;
    let mut s = body.into_data_stream();
    while let Some(chunk) = s.next().await {
        let chunk = chunk.map_err(|e| ApiError::bad_request(format!("body: {e}")))?;
        wr.write(&chunk).await?;
    }
    let out = wr.finish(Some(&expected)).await?;
    sqlx::query(
        "INSERT INTO artifacts (digest, size_bytes, worker_id) VALUES ($1, $2, $3) ON CONFLICT (digest) DO NOTHING",
    )
    .bind(out.digest.as_str())
    .bind(out.size as i64)
    .bind(&w.id)
    .execute(&st.worker_db)
    .await?;
    let status = if out.newly_created {
        StatusCode::CREATED
    } else {
        StatusCode::OK
    };
    Ok((
        status,
        Json(ArtifactPutResponse {
            digest: out.digest,
            size_bytes: out.size,
        }),
    ))
}
