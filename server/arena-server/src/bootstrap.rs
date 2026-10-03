//! Startup bootstrap: principals from the environment and signed challenges
//! from `ARENA_CHALLENGES_DIR`.

use arena_db::challenge::{self, RegisterOutcome};
use arena_db::{audit, sqlx, tier_rank, Actor};
use arena_types::{challenge::Tier, ChallengeDefinition};
use ed25519_dalek::VerifyingKey;
use serde_json::json;
use sqlx::PgPool;
use std::path::Path;

/// sha256 of a bootstrap token from `<VAR>` (plaintext) or `<VAR>_SHA256` (hex).
fn token_hash_from_env(var: &str) -> Result<Option<Vec<u8>>, String> {
    if let Ok(h) = std::env::var(format!("{var}_SHA256")) {
        let b = hex::decode(h.trim()).map_err(|_| format!("{var}_SHA256 must be hex"))?;
        if b.len() != 32 {
            return Err(format!("{var}_SHA256 must be 32 bytes"));
        }
        return Ok(Some(b));
    }
    match std::env::var(var) {
        Ok(t) if !t.trim().is_empty() => Ok(Some(arena_db::hash_token(t.trim()))),
        _ => Ok(None),
    }
}

/// Upsert bootstrap admin / worker / agent principals from the environment
/// (`ARENA_ADMIN_TOKEN[_SHA256]`, `ARENA_WORKER_TOKEN[_SHA256]`,
/// `ARENA_BOOTSTRAP_AGENT_TOKEN[_SHA256]`). Only hashes are stored.
pub async fn principals_from_env(admin_db: &PgPool, dev: bool) -> Result<(), String> {
    let sys = Actor::system();
    if let Some(h) = token_hash_from_env("ARENA_ADMIN_TOKEN")? {
        sqlx::query(
            "INSERT INTO admins (id, name, token_hash) VALUES ($1, 'bootstrap', $2)
             ON CONFLICT (name) DO UPDATE SET token_hash = EXCLUDED.token_hash",
        )
        .bind(arena_db::new_id("adm"))
        .bind(&h)
        .execute(admin_db)
        .await
        .map_err(|e| e.to_string())?;
        audit::record(
            admin_db,
            &sys,
            "admin.bootstrap",
            None,
            None,
            false,
            json!({"name": "bootstrap"}),
        )
        .await
        .map_err(|e| e.to_string())?;
    }
    if let Some(h) = token_hash_from_env("ARENA_WORKER_TOKEN")? {
        let backend = std::env::var("ARENA_BOOTSTRAP_WORKER_SANDBOX").unwrap_or_else(|_| {
            if dev {
                "bwrap-dev".into()
            } else {
                "firecracker".into()
            }
        });
        let cap = if backend == "bwrap-dev" {
            Tier::Demo
        } else {
            Tier::Formal
        };
        if !dev && backend == "bwrap-dev" {
            return Err("bwrap-dev workers are refused in production".into());
        }
        sqlx::query(
            "INSERT INTO workers (id, name, token_hash, sandbox_backend, tier_cap) VALUES ($1, 'bootstrap', $2, $3, $4)
             ON CONFLICT (name) DO UPDATE SET token_hash = EXCLUDED.token_hash,
                sandbox_backend = EXCLUDED.sandbox_backend, tier_cap = EXCLUDED.tier_cap",
        )
        .bind(arena_db::new_id("wrk"))
        .bind(&h)
        .bind(&backend)
        .bind(tier_rank(cap))
        .execute(admin_db)
        .await
        .map_err(|e| e.to_string())?;
        audit::record(
            admin_db,
            &sys,
            "worker.bootstrap",
            None,
            None,
            false,
            json!({"name": "bootstrap", "sandbox_backend": backend, "tier_cap": cap}),
        )
        .await
        .map_err(|e| e.to_string())?;
    }
    if let Some(h) = token_hash_from_env("ARENA_BOOTSTRAP_AGENT_TOKEN")? {
        let handle =
            std::env::var("ARENA_BOOTSTRAP_AGENT_HANDLE").unwrap_or_else(|_| "bootstrap".into());
        sqlx::query(
            "INSERT INTO agents (id, handle, token_hash) VALUES ($1, $2, $3)
             ON CONFLICT (handle) DO UPDATE SET token_hash = EXCLUDED.token_hash",
        )
        .bind(arena_db::new_id("agt"))
        .bind(&handle)
        .bind(&h)
        .execute(admin_db)
        .await
        .map_err(|e| e.to_string())?;
    }
    Ok(())
}

fn read_signature(path: &Path) -> Result<ed25519_dalek::Signature, String> {
    let raw = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if raw.len() == 64 {
        let arr: [u8; 64] = raw.try_into().expect("len 64");
        return Ok(ed25519_dalek::Signature::from_bytes(&arr));
    }
    challenge::parse_signature(String::from_utf8_lossy(&raw).trim())
}

/// Register every `chl_*.json` + `.sig` pair in `dir`. Challenges whose
/// signature or recomputed id fails are refused (logged, not loaded).
/// Returns (registered, refused).
pub async fn challenges_from_dir(
    admin_db: &PgPool,
    dir: &Path,
    keys: &[VerifyingKey],
    governance: &crate::Governance,
) -> Result<(usize, usize), String> {
    let mut ok = 0;
    let mut bad = 0;
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .map_err(|e| format!("{}: {e}", dir.display()))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .filter(|p| {
            p.file_stem()
                .and_then(|s| s.to_str())
                .is_some_and(|s| s.starts_with("chl_"))
        })
        .collect();
    entries.sort();
    for path in entries {
        let stem = path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or_default()
            .to_string();
        let res: Result<challenge::VerifiedChallenge, String> = (|| {
            let text = std::fs::read_to_string(&path).map_err(|e| e.to_string())?;
            let def: ChallengeDefinition =
                serde_json::from_str(&text).map_err(|e| format!("definition: {e}"))?;
            let sig = read_signature(&path.with_extension("sig"))?;
            let v = challenge::verify_definition(def, &sig, keys)?;
            for w in governance.check(&v)? {
                tracing::warn!(file = %path.display(), "{w}");
            }
            if v.id != stem {
                return Err(format!(
                    "file name {stem} does not match recomputed id {}",
                    v.id
                ));
            }
            Ok(v)
        })();
        match res {
            Ok(v) => {
                let out = challenge::register(admin_db, &v, "challenges-dir")
                    .await
                    .map_err(|e| e.to_string())?;
                if matches!(out, RegisterOutcome::Created) {
                    audit::record(
                        admin_db,
                        &Actor::system(),
                        "challenge.registered",
                        None,
                        None,
                        true,
                        json!({"challenge_id": v.id, "digest": v.digest, "source": "challenges-dir"}),
                    )
                    .await
                    .map_err(|e| e.to_string())?;
                }
                ok += 1;
            }
            Err(e) => {
                tracing::error!(file = %path.display(), "refusing challenge: {e}");
                bad += 1;
            }
        }
    }
    Ok((ok, bad))
}
