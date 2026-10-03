//! Append-only audit log. Rows can never be updated or deleted (DB trigger).
//! Public events of a submission double as its SSE event stream.

use crate::{Actor, DbError};
use serde::Serialize;
use sqlx::PgExecutor;
use time::OffsetDateTime;

#[derive(Clone, Debug, Serialize, sqlx::FromRow)]
pub struct AuditEvent {
    pub id: i64,
    #[serde(with = "time::serde::rfc3339")]
    pub at: OffsetDateTime,
    pub actor_kind: String,
    pub actor_id: String,
    pub action: String,
    pub submission_id: Option<String>,
    pub run_id: Option<String>,
    pub public: bool,
    pub data: serde_json::Value,
}

/// Record an audit event. Must be called inside the transaction performing the
/// audited change so both commit (or neither does).
pub async fn record<'e>(
    ex: impl PgExecutor<'e>,
    actor: &Actor,
    action: &str,
    submission_id: Option<&str>,
    run_id: Option<&str>,
    public: bool,
    data: serde_json::Value,
) -> Result<i64, DbError> {
    let (id,): (i64,) = sqlx::query_as(
        "INSERT INTO audit_events (actor_kind, actor_id, action, submission_id, run_id, public, data)
         VALUES ($1, $2, $3, $4, $5, $6, $7) RETURNING id",
    )
    .bind(actor.kind.as_str())
    .bind(&actor.id)
    .bind(action)
    .bind(submission_id)
    .bind(run_id)
    .bind(public)
    .bind(data)
    .fetch_one(ex)
    .await?;
    Ok(id)
}

/// Public events of a submission with id > `after`, oldest first.
pub async fn public_events_after<'e>(
    ex: impl PgExecutor<'e>,
    submission_id: &str,
    after: i64,
    limit: i64,
) -> Result<Vec<AuditEvent>, DbError> {
    Ok(sqlx::query_as(
        "SELECT id, at, actor_kind, actor_id, action, submission_id, run_id, public, data
         FROM audit_events WHERE submission_id = $1 AND public AND id > $2 ORDER BY id LIMIT $3",
    )
    .bind(submission_id)
    .bind(after)
    .bind(limit)
    .fetch_all(ex)
    .await?)
}
