use anyhow::{bail, Context};
use arena_orchestrator::signer::ReportSigner;
use arena_server::config::{Env, ServeArgs};
use arena_server::{AppState, Limits};
use arena_store::FsStore;
use arena_types::{challenge::Tier, ChallengeDefinition};
use clap::{Parser, Subcommand};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;

#[derive(Parser)]
#[command(
    name = "arena-server",
    version,
    about = "NEAR Proof Arena control plane"
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Run the public API (8471) and the internal worker API (8472).
    Serve(Box<ServeArgs>),
    /// Apply database migrations (schema owner role) and exit.
    Migrate {
        #[arg(long, env = "ARENA_MIGRATE_DATABASE_URL")]
        database_url: String,
    },
    /// Print least-privilege GRANTs for the api / worker-gateway / admin roles.
    RolesSql,
    /// Print deploy/sql/grants.sql (single control-plane role `arena_api`; workers get no DB access).
    GrantsSql,
    /// Print the OpenAPI document.
    Openapi,
    /// Create an admin principal; prints its token once.
    CreateAdmin {
        #[arg(long, env = "ARENA_DATABASE_URL")]
        database_url: String,
        #[arg(long)]
        name: String,
    },
    /// Create an agent principal; prints its token once.
    CreateAgent {
        #[arg(long, env = "ARENA_DATABASE_URL")]
        database_url: String,
        #[arg(long)]
        handle: String,
    },
    /// Register a worker; prints its token once. bwrap-dev is always capped to demo.
    CreateWorker {
        #[arg(long, env = "ARENA_DATABASE_URL")]
        database_url: String,
        #[arg(long)]
        name: String,
        #[arg(long, default_value = "firecracker")]
        sandbox: String,
        #[arg(long, default_value = "formal")]
        tier_cap: String,
    },
    /// Generate an ed25519 key (PKCS#8 PEM, mode 0600); prints the public key hex.
    Keygen {
        #[arg(long)]
        out: PathBuf,
    },
    /// Sign a challenge definition with a governance key: writes `<id>.json` and `<id>.sig` (hex).
    SignChallenge {
        #[arg(long)]
        key: PathBuf,
        #[arg(long)]
        definition: PathBuf,
        #[arg(long)]
        out_dir: PathBuf,
    },
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info,sqlx=warn".into()),
        )
        .init();
    match Cli::parse().cmd {
        Cmd::Serve(args) => serve(*args).await,
        Cmd::Migrate { database_url } => {
            let pool = arena_db::connect(&database_url, 2).await?;
            arena_db::migrate(&pool).await?;
            println!("migrations applied");
            Ok(())
        }
        Cmd::RolesSql => {
            print!(
                "{}",
                arena_db::roles::roles_script(arena_db::roles::DEFAULT_ROLES)
            );
            Ok(())
        }
        Cmd::GrantsSql => {
            print!("{}", arena_db::roles::deploy_grants_sql());
            Ok(())
        }
        Cmd::Openapi => {
            println!(
                "{}",
                serde_json::to_string_pretty(&arena_server::openapi::document())?
            );
            Ok(())
        }
        Cmd::CreateAdmin { database_url, name } => {
            let pool = arena_db::connect(&database_url, 1).await?;
            let (id, token) = arena_db::create_admin(&pool, &name).await?;
            println!("admin {id}\ntoken {token}");
            Ok(())
        }
        Cmd::CreateAgent {
            database_url,
            handle,
        } => {
            let pool = arena_db::connect(&database_url, 1).await?;
            let (id, token) = arena_db::create_agent(&pool, &handle).await?;
            println!("agent {id}\ntoken {token}");
            Ok(())
        }
        Cmd::CreateWorker {
            database_url,
            name,
            sandbox,
            tier_cap,
        } => {
            let tier: Tier = arena_db::parse_enum(&tier_cap)?;
            let tier = if sandbox == "bwrap-dev" {
                Tier::Demo
            } else {
                tier
            };
            let pool = arena_db::connect(&database_url, 1).await?;
            let (id, token) = arena_db::create_worker(&pool, &name, &sandbox, tier).await?;
            println!("worker {id} ({sandbox}, tier cap {tier:?})\ntoken {token}");
            Ok(())
        }
        Cmd::Keygen { out } => {
            let (pem, pk) = ReportSigner::generate_pem();
            arena_server::config::write_secret(&out, &pem).map_err(anyhow::Error::msg)?;
            println!("{pk}");
            Ok(())
        }
        Cmd::SignChallenge {
            key,
            definition,
            out_dir,
        } => {
            use ed25519_dalek::pkcs8::DecodePrivateKey;
            use ed25519_dalek::Signer;
            let pem = std::fs::read_to_string(&key)?;
            let k =
                ed25519_dalek::SigningKey::from_pkcs8_pem(pem.trim()).context("governance key")?;
            let def: ChallengeDefinition =
                serde_json::from_str(&std::fs::read_to_string(&definition)?)?;
            let bytes = arena_types::canonical_json(&def)?;
            let id = def.id()?;
            std::fs::create_dir_all(&out_dir)?;
            std::fs::write(
                out_dir.join(format!("{id}.json")),
                serde_json::to_string_pretty(&def)? + "\n",
            )?;
            std::fs::write(
                out_dir.join(format!("{id}.sig")),
                hex::encode(k.sign(&bytes).to_bytes()) + "\n",
            )?;
            println!("{id}");
            Ok(())
        }
    }
}

async fn serve(args: ServeArgs) -> anyhow::Result<()> {
    let mut r = args
        .resolve()
        .map_err(|e| anyhow::anyhow!("refusing to start: {e}"))?;
    let dev = r.env == Env::Dev;
    tracing::info!(env = ?r.env, report_key = %r.signer.public_key_hex(), governance_keys = r.governance_keys.len(), "starting");
    let api_db = arena_db::connect(&args.database_url, 32)
        .await
        .context("connect ARENA_DATABASE_URL")?;
    let worker_db = match &args.worker_gateway_database_url {
        Some(u) => arena_db::connect(u, 16)
            .await
            .context("connect worker gateway DB")?,
        None => api_db.clone(),
    };
    let admin_db = match &args.admin_database_url {
        Some(u) => arena_db::connect(u, 4).await.context("connect admin DB")?,
        None => api_db.clone(),
    };
    if arena_db::sqlx::query("SELECT 1 FROM runs LIMIT 0")
        .execute(&api_db)
        .await
        .is_err()
    {
        bail!("database schema missing; run `arena-server migrate` first");
    }
    let l = &args.limits;
    let store = FsStore::open(
        &args.object_store_dir,
        l.max_upload_bytes.max(l.max_artifact_bytes),
    )?;
    arena_server::bootstrap::principals_from_env(&admin_db, dev)
        .await
        .map_err(anyhow::Error::msg)?;
    let governance = arena_server::Governance {
        dev_only_keys: r.dev_only_keys.clone(),
        governed: r.governed.take(),
    };
    if let Some(dir) = &args.challenges_dir {
        let (ok, bad) = arena_server::bootstrap::challenges_from_dir(
            &admin_db,
            dir,
            &r.governance_keys,
            &governance,
        )
        .await
        .map_err(anyhow::Error::msg)?;
        tracing::info!(registered = ok, refused = bad, dir = %dir.display(), "challenges loaded");
    }
    let orch_cfg = arena_orchestrator::Config {
        max_attempts: l.max_attempts.max(1),
        retry_backoff: Duration::from_secs(l.retry_backoff_secs),
        lease_default: Duration::from_secs(l.lease_secs),
        ..Default::default()
    };
    let limits = Limits {
        max_upload_bytes: l.max_upload_bytes,
        max_artifact_bytes: l.max_artifact_bytes,
        submissions_per_day: l.submissions_per_day,
        upload_bytes_per_day: l.upload_bytes_per_day,
        active_runs: l.active_runs,
        rate_per_minute: l.rate_per_minute,
        ..Default::default()
    };
    let state = Arc::new(AppState {
        api_db,
        worker_db,
        admin_db,
        store: Arc::new(store),
        orch: Arc::new(arena_orchestrator::Orchestrator::new(
            orch_cfg,
            Arc::new(r.signer),
            Arc::new(r.governance_keys),
        )),
        rate: arena_server::ratelimit::RateLimiter::new(limits.rate_per_minute, limits.rate_burst),
        limits,
        governance,
        dev,
    });
    arena_server::spawn_reaper(state.clone(), Duration::from_secs(5));
    let public = tokio::net::TcpListener::bind(r.bind)
        .await
        .with_context(|| format!("bind {}", r.bind))?;
    let internal = tokio::net::TcpListener::bind(r.worker_bind)
        .await
        .with_context(|| format!("bind {}", r.worker_bind))?;
    tracing::info!(public = %r.bind, worker = %r.worker_bind, "listening");
    // Graceful shutdown on SIGINT or SIGTERM (containers/systemd send SIGTERM).
    let shutdown = || async {
        #[cfg(unix)]
        {
            let mut term =
                tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())
                    .expect("install SIGTERM handler");
            tokio::select! {
                _ = tokio::signal::ctrl_c() => {}
                _ = term.recv() => {}
            }
        }
        #[cfg(not(unix))]
        let _ = tokio::signal::ctrl_c().await;
        tracing::info!("shutting down");
    };
    let a = axum::serve(public, arena_server::public_router(state.clone()))
        .with_graceful_shutdown(shutdown());
    let b = axum::serve(internal, arena_server::worker_router(state))
        .with_graceful_shutdown(shutdown());
    tokio::try_join!(async { a.await }, async { b.await })?;
    Ok(())
}
