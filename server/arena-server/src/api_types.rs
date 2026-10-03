//! Request/response bodies of the HTTP API that are not frozen contract types.

use arena_types::{challenge::Tier, ChallengeDefinition, Digest};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct UploadResponse {
    pub upload_id: String,
    pub digest: Digest,
    pub size_bytes: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct SubmitRequest {
    pub challenge_id: String,
    pub upload_digest: Digest,
    /// Unique per agent; `[A-Za-z0-9._:-]{1,128}`. Replaying the same key with the
    /// same body returns the original submission; a different body is a 409.
    pub idempotency_key: String,
    #[serde(default)]
    pub parent: Option<String>,
}

#[derive(Clone, Debug, Default, Deserialize, JsonSchema)]
pub struct SubmissionsQuery {
    pub challenge_id: Option<String>,
    /// Agent handle.
    pub agent: Option<String>,
    /// 1..=500, default 100.
    pub limit: Option<i64>,
    /// Keyset pagination: only submissions created before this submission id.
    pub before: Option<String>,
}

#[derive(Clone, Debug, Default, Deserialize, JsonSchema)]
pub struct EventsQuery {
    /// Resume after this event id (alternative to the `Last-Event-ID` header).
    pub after: Option<i64>,
}

/// Data of one SSE event (`id:` = event id, `event:` = kind).
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct EventPayload {
    pub id: i64,
    pub at: String,
    /// Raw audit action, e.g. `run.stage`, `gate.result`, `run.decided`.
    pub action: String,
    pub run_id: Option<String>,
    pub data: serde_json::Value,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct RegisterChallengeRequest {
    pub definition: ChallengeDefinition,
    /// ed25519 signature (hex or base64) over the JCS bytes of `definition`
    /// by a configured governance key.
    pub signature: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct RegisterChallengeResponse {
    pub id: String,
    pub digest: Digest,
    /// `false` if the identical challenge was already registered.
    pub created: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ChallengeStatusRequest {
    /// Whether new submissions are accepted.
    pub open: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ReasonRequest {
    /// Shown publicly; plain text, bounded.
    pub reason: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct RerunResponse {
    pub submission_id: String,
    pub run_id: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct InvalidateCacheRequest {
    pub checker_image: Option<Digest>,
    pub assumption: Option<String>,
    pub reason: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct InvalidateCacheResponse {
    pub invalidated: Vec<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CreateAgentRequest {
    /// `[a-z0-9][a-z0-9_-]{0,47}`
    pub handle: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CreateWorkerRequest {
    pub name: String,
    /// e.g. `firecracker`, `bwrap-dev` (always capped to `demo`).
    pub sandbox_backend: String,
    /// Highest challenge tier this worker may be leased.
    pub tier_cap: Tier,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct CreatedPrincipal {
    pub id: String,
    pub name: String,
    /// Shown once; only its sha256 is stored.
    pub token: String,
}

#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct QuotaRequest {
    pub max_submissions_per_day: i32,
    pub max_upload_bytes_per_day: i64,
    pub max_active_runs: i32,
}

#[derive(Clone, Debug, Default, Deserialize, JsonSchema)]
pub struct AuditQuery {
    pub submission_id: Option<String>,
    pub after: Option<i64>,
    pub limit: Option<i64>,
}
