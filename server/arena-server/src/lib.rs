//! NEAR Proof Arena control-plane HTTP server.
//!
//! Two listeners:
//! * the **public API** (`/v1/...`, default `127.0.0.1:8471`): read-only views,
//!   agent uploads/submissions/cancellation, and admin endpoints (`/v1/admin/...`,
//!   separate admin tokens);
//! * the **internal worker API** (`/internal/v1/...`, default `127.0.0.1:8472`):
//!   lease/heartbeat/complete/fail jobs and get/put artifacts by digest, with
//!   worker tokens. Workers never get database credentials or the report key.

pub mod admin;
pub mod api_types;
pub mod auth;
pub mod bootstrap;
pub mod config;
pub mod error;
pub mod openapi;
pub mod public;
pub mod ratelimit;
pub mod worker;

use arena_orchestrator::Orchestrator;
use arena_store::ObjectStore;
use axum::http::{header, HeaderValue};
use axum::Router;
use sqlx::PgPool;
use std::sync::Arc;
use std::time::Duration;
use tower_http::set_header::SetResponseHeaderLayer;

/// Request/size/quota limits.
#[derive(Clone, Debug)]
pub struct Limits {
    pub max_upload_bytes: u64,
    pub max_artifact_bytes: u64,
    pub max_json_bytes: usize,
    pub submissions_per_day: i64,
    pub upload_bytes_per_day: i64,
    pub active_runs: i64,
    pub rate_per_minute: u32,
    pub rate_burst: u32,
    pub sse_poll: Duration,
    pub sse_max_duration: Duration,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_upload_bytes: 256 << 20,
            max_artifact_bytes: 2 << 30,
            max_json_bytes: 1 << 20,
            submissions_per_day: 50,
            upload_bytes_per_day: 4 << 30,
            active_runs: 4,
            rate_per_minute: 120,
            rate_burst: 60,
            sse_poll: Duration::from_millis(500),
            sse_max_duration: Duration::from_secs(3600),
        }
    }
}

pub struct AppState {
    /// Pool for the public/agent API (`arena_api` role).
    pub api_db: PgPool,
    /// Pool for the worker gateway (`arena_worker` role in split-role deployments).
    pub worker_db: PgPool,
    /// Pool for admin endpoints (`arena_admin` role in split-role deployments).
    pub admin_db: PgPool,
    pub store: Arc<dyn ObjectStore>,
    pub orch: Arc<Orchestrator>,
    pub limits: Limits,
    pub rate: ratelimit::RateLimiter,
    pub dev: bool,
}

pub type SharedState = Arc<AppState>;

fn security_headers<S: Clone + Send + Sync + 'static>(r: Router<S>) -> Router<S> {
    r.layer(SetResponseHeaderLayer::overriding(
        header::X_CONTENT_TYPE_OPTIONS,
        HeaderValue::from_static("nosniff"),
    ))
    .layer(SetResponseHeaderLayer::overriding(
        header::CONTENT_SECURITY_POLICY,
        HeaderValue::from_static("default-src 'none'; frame-ancestors 'none'"),
    ))
    .layer(SetResponseHeaderLayer::overriding(
        header::REFERRER_POLICY,
        HeaderValue::from_static("no-referrer"),
    ))
}

/// Router for the public listener (`/v1`, `/healthz`).
pub fn public_router(state: SharedState) -> Router {
    let r = Router::new()
        .merge(public::routes(&state))
        .merge(admin::routes(&state))
        .with_state(state);
    security_headers(r)
}

/// Router for the internal worker listener (`/internal/v1`).
pub fn worker_router(state: SharedState) -> Router {
    security_headers(worker::routes(&state).with_state(state))
}

/// Background task: fail jobs whose lease expired on their final attempt.
pub fn spawn_reaper(state: SharedState, every: Duration) -> tokio::task::JoinHandle<()> {
    tokio::spawn(async move {
        let mut tick = tokio::time::interval(every);
        loop {
            tick.tick().await;
            match state.orch.reap_expired(&state.worker_db).await {
                Ok(0) => {}
                Ok(n) => tracing::warn!(reaped = n, "jobs failed after final lease expiry"),
                Err(e) => tracing::error!("reaper: {e}"),
            }
        }
    })
}
