//! Bearer-token extractors. Tokens are looked up by their sha256 hash in the
//! table of the expected principal kind only: an agent token is never valid
//! on admin or worker endpoints and vice versa.

use crate::error::ApiError;
use crate::SharedState;
use arena_db::{AdminRow, AgentRow, WorkerRow};
use axum::extract::FromRequestParts;
use axum::http::{header, request::Parts};

fn bearer(parts: &Parts) -> Option<&str> {
    let v = parts.headers.get(header::AUTHORIZATION)?.to_str().ok()?;
    let t = v
        .strip_prefix("Bearer ")
        .or_else(|| v.strip_prefix("bearer "))?
        .trim();
    (!t.is_empty() && t.len() <= 512).then_some(t)
}

pub struct AgentAuth(pub AgentRow);
pub struct AdminAuth(pub AdminRow);
pub struct WorkerAuth(pub WorkerRow);

impl FromRequestParts<SharedState> for AgentAuth {
    type Rejection = ApiError;
    async fn from_request_parts(parts: &mut Parts, st: &SharedState) -> Result<Self, ApiError> {
        let t = bearer(parts).ok_or_else(ApiError::unauthorized)?;
        let a = arena_db::agent_by_token(&st.api_db, t)
            .await?
            .ok_or_else(ApiError::unauthorized)?;
        if a.disabled {
            return Err(ApiError::forbidden("agent disabled"));
        }
        st.rate
            .check(&a.id)
            .map_err(|s| ApiError::too_many("rate_limited", "per-agent rate limit exceeded", s))?;
        Ok(AgentAuth(a))
    }
}

impl FromRequestParts<SharedState> for AdminAuth {
    type Rejection = ApiError;
    async fn from_request_parts(parts: &mut Parts, st: &SharedState) -> Result<Self, ApiError> {
        let t = bearer(parts).ok_or_else(ApiError::unauthorized)?;
        let a = arena_db::admin_by_token(&st.admin_db, t)
            .await?
            .ok_or_else(ApiError::unauthorized)?;
        if a.disabled {
            return Err(ApiError::forbidden("admin disabled"));
        }
        Ok(AdminAuth(a))
    }
}

impl FromRequestParts<SharedState> for WorkerAuth {
    type Rejection = ApiError;
    async fn from_request_parts(parts: &mut Parts, st: &SharedState) -> Result<Self, ApiError> {
        let t = bearer(parts).ok_or_else(ApiError::unauthorized)?;
        let w = arena_db::worker_by_token(&st.worker_db, t)
            .await?
            .ok_or_else(ApiError::unauthorized)?;
        if w.disabled {
            return Err(ApiError::forbidden("worker disabled"));
        }
        Ok(WorkerAuth(w))
    }
}
