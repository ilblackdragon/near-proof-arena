use arena_orchestrator::OrchError;
use axum::http::{header, StatusCode};
use axum::response::{IntoResponse, Response};
use axum::Json;
use serde_json::json;

/// JSON error: `{"error": {"code": "...", "message": "..."}}`.
#[derive(Debug)]
pub struct ApiError {
    pub status: StatusCode,
    pub code: &'static str,
    pub message: String,
    pub retry_after: Option<u64>,
}

impl ApiError {
    pub fn new(status: StatusCode, code: &'static str, message: impl Into<String>) -> Self {
        Self { status, code, message: message.into(), retry_after: None }
    }
    pub fn bad_request(m: impl Into<String>) -> Self {
        Self::new(StatusCode::BAD_REQUEST, "bad_request", m)
    }
    pub fn not_found(m: impl Into<String>) -> Self {
        Self::new(StatusCode::NOT_FOUND, "not_found", m)
    }
    pub fn conflict(code: &'static str, m: impl Into<String>) -> Self {
        Self::new(StatusCode::CONFLICT, code, m)
    }
    pub fn unauthorized() -> Self {
        Self::new(StatusCode::UNAUTHORIZED, "unauthorized", "missing or invalid bearer token")
    }
    pub fn forbidden(m: impl Into<String>) -> Self {
        Self::new(StatusCode::FORBIDDEN, "forbidden", m)
    }
    pub fn too_many(code: &'static str, m: impl Into<String>, retry_after: u64) -> Self {
        Self { retry_after: Some(retry_after), ..Self::new(StatusCode::TOO_MANY_REQUESTS, code, m) }
    }
    pub fn internal(e: impl std::fmt::Display) -> Self {
        let id = uuid::Uuid::new_v4();
        tracing::error!(error_id = %id, "internal error: {e}");
        Self::new(StatusCode::INTERNAL_SERVER_ERROR, "internal", format!("internal error (id {id})"))
    }
}

impl IntoResponse for ApiError {
    fn into_response(self) -> Response {
        let mut r = (self.status, Json(json!({"error": {"code": self.code, "message": self.message}})))
            .into_response();
        if let Some(s) = self.retry_after {
            r.headers_mut().insert(header::RETRY_AFTER, s.into());
        }
        r
    }
}

impl From<arena_db::DbError> for ApiError {
    fn from(e: arena_db::DbError) -> Self {
        match e {
            arena_db::DbError::ChallengeIntegrity { .. } => {
                tracing::error!("{e}");
                ApiError::new(StatusCode::INTERNAL_SERVER_ERROR, "challenge_integrity", e.to_string())
            }
            other => ApiError::internal(other),
        }
    }
}

impl From<sqlx::Error> for ApiError {
    fn from(e: sqlx::Error) -> Self {
        if let Some(db) = e.as_database_error() {
            if db.is_unique_violation() {
                return ApiError::conflict("already_exists", "a record with these unique fields already exists");
            }
            if db.is_check_violation() {
                return ApiError::bad_request(format!("constraint violated: {}", db.constraint().unwrap_or("?")));
            }
        }
        ApiError::internal(e)
    }
}

impl From<OrchError> for ApiError {
    fn from(e: OrchError) -> Self {
        match e {
            OrchError::NotFound(m) => ApiError::not_found(m),
            OrchError::LeaseLost => ApiError::conflict("lease_lost", e.to_string()),
            OrchError::Cancelled => ApiError::conflict("cancelled", e.to_string()),
            OrchError::InvalidResult(m) => ApiError::new(
                StatusCode::UNPROCESSABLE_ENTITY,
                "invalid_result",
                format!("{m} (attempt recorded as an infrastructure failure)"),
            ),
            OrchError::Conflict(m) => ApiError::conflict("conflict", m),
            OrchError::Db(d) => d.into(),
        }
    }
}

impl From<arena_store::StoreError> for ApiError {
    fn from(e: arena_store::StoreError) -> Self {
        use arena_store::StoreError::*;
        match e {
            TooLarge { limit } => ApiError::new(
                StatusCode::PAYLOAD_TOO_LARGE,
                "too_large",
                format!("object exceeds the {limit}-byte limit"),
            ),
            DigestMismatch { .. } => ApiError::bad_request(e.to_string()),
            other => ApiError::internal(other),
        }
    }
}

pub type ApiResult<T> = Result<T, ApiError>;
