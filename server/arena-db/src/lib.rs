//! Postgres schema, migrations, least-privilege roles and data access for the
//! NEAR Proof Arena control plane.
//!
//! All queries are runtime-checked (`sqlx::query`), so building this crate
//! never needs a `DATABASE_URL`.

pub mod audit;
pub mod challenge;
pub mod roles;
pub mod views;

use arena_types::challenge::Tier;
use serde::{de::DeserializeOwned, Serialize};
use sha2::{Digest as _, Sha256};
use sqlx::postgres::{PgPool, PgPoolOptions};
use time::OffsetDateTime;

pub use sqlx;

pub static MIGRATOR: sqlx::migrate::Migrator = sqlx::migrate!("./migrations");

#[derive(Debug, thiserror::Error)]
pub enum DbError {
    #[error("database: {0}")]
    Sqlx(#[from] sqlx::Error),
    #[error("migration: {0}")]
    Migrate(#[from] sqlx::migrate::MigrateError),
    #[error("stored data is invalid: {0}")]
    Corrupt(String),
    #[error("challenge integrity check failed for {id}: {why}")]
    ChallengeIntegrity { id: String, why: String },
}

impl DbError {
    pub fn corrupt(e: impl std::fmt::Display) -> Self {
        DbError::Corrupt(e.to_string())
    }
}

pub async fn connect(url: &str, max_connections: u32) -> Result<PgPool, DbError> {
    Ok(PgPoolOptions::new()
        .max_connections(max_connections)
        .acquire_timeout(std::time::Duration::from_secs(10))
        .connect(url)
        .await?)
}

pub async fn migrate(pool: &PgPool) -> Result<(), DbError> {
    MIGRATOR.run(pool).await?;
    Ok(())
}

// ------------------------------------------------------------------ helpers

/// Serialize a unit-variant enum to its serde string form (e.g. `Stage::Built` -> `"BUILT"`).
pub fn enum_str<T: Serialize>(v: &T) -> String {
    match serde_json::to_value(v) {
        Ok(serde_json::Value::String(s)) => s,
        other => panic!("enum_str on non-string enum: {other:?}"),
    }
}

pub fn parse_enum<T: DeserializeOwned>(s: &str) -> Result<T, DbError> {
    serde_json::from_value(serde_json::Value::String(s.to_string()))
        .map_err(|e| DbError::Corrupt(format!("bad enum value {s:?}: {e}")))
}

pub fn tier_rank(t: Tier) -> i16 {
    match t {
        Tier::Demo => 0,
        Tier::Experimental => 1,
        Tier::Formal => 2,
    }
}

pub fn tier_from_rank(r: i16) -> Tier {
    match r {
        2 => Tier::Formal,
        1 => Tier::Experimental,
        _ => Tier::Demo,
    }
}

/// The lower (less trusted) of two tiers.
pub fn tier_min(a: Tier, b: Tier) -> Tier {
    if tier_rank(a) <= tier_rank(b) {
        a
    } else {
        b
    }
}

/// `<prefix>_<32 hex>` identifier.
pub fn new_id(prefix: &str) -> String {
    format!("{prefix}_{}", uuid::Uuid::new_v4().simple())
}

/// A fresh bearer token: `arena_<kind>_<43 chars base64url(32 random bytes)>`.
pub fn generate_token(kind: &str) -> String {
    use base64::Engine;
    use rand::RngCore;
    let mut b = [0u8; 32];
    rand::rngs::OsRng.fill_bytes(&mut b);
    format!("arena_{kind}_{}", base64::engine::general_purpose::URL_SAFE_NO_PAD.encode(b))
}

/// Tokens are stored only as sha256 hashes.
pub fn hash_token(token: &str) -> Vec<u8> {
    Sha256::digest(token.as_bytes()).to_vec()
}

pub fn rfc3339(t: OffsetDateTime) -> String {
    t.format(&time::format_description::well_known::Rfc3339).expect("rfc3339 formatting")
}

pub fn json<T: Serialize>(v: &T) -> serde_json::Value {
    serde_json::to_value(v).expect("serializable")
}

pub fn from_json<T: DeserializeOwned>(v: serde_json::Value) -> Result<T, DbError> {
    serde_json::from_value(v).map_err(DbError::corrupt)
}

pub fn from_json_opt<T: DeserializeOwned>(v: Option<serde_json::Value>) -> Result<Option<T>, DbError> {
    v.map(from_json).transpose()
}

// ------------------------------------------------------------------ principals

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ActorKind {
    Agent,
    Admin,
    Worker,
    System,
}

impl ActorKind {
    pub fn as_str(self) -> &'static str {
        match self {
            ActorKind::Agent => "agent",
            ActorKind::Admin => "admin",
            ActorKind::Worker => "worker",
            ActorKind::System => "system",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Actor {
    pub kind: ActorKind,
    pub id: String,
}

impl Actor {
    pub fn system() -> Self {
        Actor { kind: ActorKind::System, id: "control-plane".into() }
    }
    pub fn agent(id: &str) -> Self {
        Actor { kind: ActorKind::Agent, id: id.into() }
    }
    pub fn admin(id: &str) -> Self {
        Actor { kind: ActorKind::Admin, id: id.into() }
    }
    pub fn worker(id: &str) -> Self {
        Actor { kind: ActorKind::Worker, id: id.into() }
    }
}

#[derive(Clone, Debug, sqlx::FromRow)]
pub struct AgentRow {
    pub id: String,
    pub handle: String,
    pub disabled: bool,
}

#[derive(Clone, Debug, sqlx::FromRow)]
pub struct AdminRow {
    pub id: String,
    pub name: String,
    pub disabled: bool,
}

#[derive(Clone, Debug, sqlx::FromRow)]
pub struct WorkerRow {
    pub id: String,
    pub name: String,
    pub sandbox_backend: String,
    pub tier_cap: i16,
    pub disabled: bool,
}

pub async fn agent_by_token(pool: &PgPool, token: &str) -> Result<Option<AgentRow>, DbError> {
    Ok(sqlx::query_as("SELECT id, handle, disabled FROM agents WHERE token_hash = $1")
        .bind(hash_token(token))
        .fetch_optional(pool)
        .await?)
}

pub async fn admin_by_token(pool: &PgPool, token: &str) -> Result<Option<AdminRow>, DbError> {
    Ok(sqlx::query_as("SELECT id, name, disabled FROM admins WHERE token_hash = $1")
        .bind(hash_token(token))
        .fetch_optional(pool)
        .await?)
}

pub async fn worker_by_token(pool: &PgPool, token: &str) -> Result<Option<WorkerRow>, DbError> {
    Ok(sqlx::query_as(
        "SELECT id, name, sandbox_backend, tier_cap, disabled FROM workers WHERE token_hash = $1",
    )
    .bind(hash_token(token))
    .fetch_optional(pool)
    .await?)
}

/// Create an agent; returns `(agent_id, token)`. The token is shown once.
pub async fn create_agent(pool: &PgPool, handle: &str) -> Result<(String, String), DbError> {
    let id = new_id("agt");
    let token = generate_token("agt");
    sqlx::query("INSERT INTO agents (id, handle, token_hash) VALUES ($1, $2, $3)")
        .bind(&id)
        .bind(handle)
        .bind(hash_token(&token))
        .execute(pool)
        .await?;
    Ok((id, token))
}

pub async fn create_admin(pool: &PgPool, name: &str) -> Result<(String, String), DbError> {
    let id = new_id("adm");
    let token = generate_token("adm");
    sqlx::query("INSERT INTO admins (id, name, token_hash) VALUES ($1, $2, $3)")
        .bind(&id)
        .bind(name)
        .bind(hash_token(&token))
        .execute(pool)
        .await?;
    Ok((id, token))
}

/// Register a worker. `bwrap-dev` workers are always capped at the demo tier
/// (also enforced by a CHECK constraint).
pub async fn create_worker(
    pool: &PgPool,
    name: &str,
    sandbox_backend: &str,
    tier_cap: Tier,
) -> Result<(String, String), DbError> {
    let id = new_id("wrk");
    let token = generate_token("wrk");
    sqlx::query(
        "INSERT INTO workers (id, name, token_hash, sandbox_backend, tier_cap) VALUES ($1, $2, $3, $4, $5)",
    )
    .bind(&id)
    .bind(name)
    .bind(hash_token(&token))
    .bind(sandbox_backend)
    .bind(tier_rank(tier_cap))
    .execute(pool)
    .await?;
    Ok((id, token))
}

#[cfg(test)]
mod tests {
    use super::*;
    use arena_types::{Decision, Stage};
    #[test]
    fn enum_roundtrip() {
        assert_eq!(enum_str(&Stage::FormalChecked), "FORMAL_CHECKED");
        assert_eq!(parse_enum::<Decision>("INFRA_ERROR").unwrap(), Decision::InfraError);
        assert_eq!(enum_str(&Tier::Formal), "formal");
        assert!(parse_enum::<Decision>("nope").is_err());
    }
    #[test]
    fn tokens() {
        let t = generate_token("agt");
        assert!(t.starts_with("arena_agt_") && t.len() == 10 + 43);
        assert_eq!(hash_token(&t).len(), 32);
        assert_ne!(generate_token("agt"), t);
    }
    #[test]
    fn tiers() {
        assert_eq!(tier_min(Tier::Formal, Tier::Demo), Tier::Demo);
        for t in [Tier::Demo, Tier::Experimental, Tier::Formal] {
            assert_eq!(tier_from_rank(tier_rank(t)), t);
        }
    }
}
