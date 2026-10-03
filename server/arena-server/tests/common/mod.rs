//! Integration-test harness: a fresh `arena_server_test_*` database per test,
//! both listeners on ephemeral loopback ports, and an in-process FAKE worker
//! whose results are always tier DEMO (it performs no real checks).

#![allow(dead_code)]

pub mod fake_worker;

use arena_db::sqlx::{self, PgPool};
use arena_orchestrator::signer::ReportSigner;
use arena_orchestrator::Orchestrator;
use arena_server::{AppState, Limits, SharedState};
use arena_store::FsStore;
use arena_types::challenge::*;
use arena_types::security::*;
use arena_types::{ChallengeDefinition, Digest, ObligationId, SubmissionView};
use ed25519_dalek::{Signer, SigningKey};
use serde_json::{json, Value};
use std::sync::Arc;
use std::time::Duration;

pub const REPORT_SEED_HEX: &str =
    "4f3c2b1a09887766554433221100ffeeddccbbaa99887766554433221100ff11";

pub fn base_url() -> String {
    std::env::var("ARENA_TEST_DATABASE_URL")
        .unwrap_or_else(|_| "postgres://arena:arena@127.0.0.1:55471/postgres".to_string())
}

fn db_url(name: &str) -> String {
    let base = base_url();
    let i = base.rfind('/').expect("db url");
    format!("{}/{name}", &base[..i])
}

/// Drops the test database even if the test panics.
pub struct DbGuard {
    pub name: String,
    pub roles: Vec<String>,
}

impl Drop for DbGuard {
    fn drop(&mut self) {
        let name = self.name.clone();
        let roles = self.roles.clone();
        let _ = std::thread::spawn(move || {
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .unwrap();
            rt.block_on(async {
                if let Ok(p) = arena_db::connect(&base_url(), 1).await {
                    let _ = sqlx::query(&format!("DROP DATABASE IF EXISTS {name} WITH (FORCE)"))
                        .execute(&p)
                        .await;
                    for r in roles {
                        let _ = sqlx::query(&format!("DROP ROLE IF EXISTS {r}"))
                            .execute(&p)
                            .await;
                    }
                }
            });
        })
        .join();
    }
}

pub struct Opts {
    pub limits: Limits,
    pub max_attempts: i32,
    pub lease_default: Duration,
    /// Serve through three pools that `SET ROLE` to freshly created
    /// least-privilege api / worker-gateway / admin roles.
    pub split_roles: bool,
    /// With `split_roles`: use one role with the single-role (deployment)
    /// grants for all three pools instead.
    pub single_role: bool,
}

impl Default for Opts {
    fn default() -> Self {
        Self {
            limits: Limits {
                sse_poll: Duration::from_millis(50),
                rate_per_minute: 0, // disabled unless a test enables it
                ..Default::default()
            },
            max_attempts: 3,
            lease_default: Duration::from_secs(60),
            split_roles: false,
            single_role: false,
        }
    }
}

pub struct TestApp {
    pub base: String,
    pub worker_base: String,
    pub state: SharedState,
    pub pool: PgPool,
    pub db_url: String,
    pub http: reqwest::Client,
    pub gov: SigningKey,
    pub admin_token: String,
    pub agent_token: String,
    pub agent2_token: String,
    pub worker_token: String,
    pub store_dir: tempfile::TempDir,
    pub _guard: DbGuard,
}

pub async fn spawn() -> TestApp {
    spawn_with(Opts::default()).await
}

pub async fn spawn_with(opts: Opts) -> TestApp {
    let _ = tracing_subscriber::fmt()
        .with_test_writer()
        .with_env_filter("warn")
        .try_init();
    let name = format!(
        "arena_server_test_{}",
        &uuid::Uuid::new_v4().simple().to_string()[..16]
    );
    let root = arena_db::connect(&base_url(), 1)
        .await
        .expect("connect to shared Postgres");
    sqlx::query(&format!("CREATE DATABASE {name}"))
        .execute(&root)
        .await
        .unwrap();
    root.close().await;
    let mut guard = DbGuard {
        name: name.clone(),
        roles: vec![],
    };
    let url = db_url(&name);
    let pool = arena_db::connect(&url, 16).await.unwrap();
    arena_db::migrate(&pool).await.unwrap();
    let (api_db, worker_db, admin_db) = if opts.split_roles {
        let sfx = &name["arena_server_test_".len()..];
        let names: Vec<String> = ["api", "wrk", "adm"]
            .iter()
            .map(|k| format!("arena_server_test_{k}_{sfx}"))
            .collect();
        for n in &names {
            sqlx::query(&format!("CREATE ROLE {n} NOLOGIN"))
                .execute(&pool)
                .await
                .expect("CREATEROLE needed");
            guard.roles.push(n.clone());
            sqlx::query(&format!("GRANT {n} TO CURRENT_USER"))
                .execute(&pool)
                .await
                .unwrap();
        }
        let roles = arena_db::roles::RoleNames {
            api: &names[0],
            worker: &names[1],
            admin: &names[2],
        };
        let sql = if opts.single_role {
            arena_db::roles::single_role_grants_sql(&names[0], &[&names[1]])
        } else {
            arena_db::roles::grants_sql(roles)
        };
        sqlx::raw_sql(&sql).execute(&pool).await.unwrap();
        let mk = |role: String| {
            let url = url.clone();
            async move {
                arena_db::sqlx::postgres::PgPoolOptions::new()
                    .max_connections(8)
                    .after_connect(move |conn, _| {
                        let role = role.clone();
                        Box::pin(async move {
                            sqlx::query(&format!("SET ROLE {role}"))
                                .execute(&mut *conn)
                                .await?;
                            Ok(())
                        })
                    })
                    .connect(&url)
                    .await
                    .unwrap()
            }
        };
        if opts.single_role {
            let p = mk(names[0].clone()).await;
            (p.clone(), p.clone(), p)
        } else {
            (
                mk(names[0].clone()).await,
                mk(names[1].clone()).await,
                mk(names[2].clone()).await,
            )
        }
    } else {
        (pool.clone(), pool.clone(), pool.clone())
    };

    let gov = SigningKey::from_bytes(&[7u8; 32]);
    let store_dir = tempfile::tempdir().unwrap();
    let store = FsStore::open(store_dir.path(), 64 << 20).unwrap();
    let cfg = arena_orchestrator::Config {
        max_attempts: opts.max_attempts,
        retry_backoff: Duration::ZERO,
        lease_default: opts.lease_default,
        lease_min: Duration::from_secs(1),
        lease_max: Duration::from_secs(600),
    };
    let signer = ReportSigner::from_hex(REPORT_SEED_HEX).unwrap();
    let state: SharedState = Arc::new(AppState {
        api_db,
        worker_db,
        admin_db,
        store: Arc::new(store),
        orch: Arc::new(Orchestrator::new(
            cfg,
            Arc::new(signer),
            Arc::new(vec![gov.verifying_key()]),
        )),
        rate: arena_server::ratelimit::RateLimiter::new(
            opts.limits.rate_per_minute,
            opts.limits.rate_burst,
        ),
        limits: opts.limits,
        dev: true,
    });
    let public = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let internal = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let base = format!("http://{}", public.local_addr().unwrap());
    let worker_base = format!("http://{}", internal.local_addr().unwrap());
    tokio::spawn(std::future::IntoFuture::into_future(axum::serve(
        public,
        arena_server::public_router(state.clone()),
    )));
    tokio::spawn(std::future::IntoFuture::into_future(axum::serve(
        internal,
        arena_server::worker_router(state.clone()),
    )));

    let (_, admin_token) = arena_db::create_admin(&pool, "root").await.unwrap();
    let (_, agent_token) = arena_db::create_agent(&pool, "alice").await.unwrap();
    let (_, agent2_token) = arena_db::create_agent(&pool, "bob").await.unwrap();
    // The fake worker is registered as demo-capped: it can only ever be leased demo-tier work.
    let (_, worker_token) = arena_db::create_worker(&pool, "fake", "test-fake", Tier::Demo)
        .await
        .unwrap();
    TestApp {
        base,
        worker_base,
        state,
        pool,
        db_url: url,
        http: reqwest::Client::new(),
        gov,
        admin_token,
        agent_token,
        agent2_token,
        worker_token,
        store_dir,
        _guard: guard,
    }
}

pub fn all_obligations() -> Vec<ObligationId> {
    use ObligationId::*;
    vec![
        PkgWellformed,
        BuildReproducible,
        ArtifactBinding,
        FormalSemanticSoundness,
        FormalSemanticCompleteness,
        FormalCryptoSoundness,
        FormalImplConnection,
        FormalZk,
        AxiomAudit,
        ConformanceDifferential,
        AdversarialProofs,
        ProverReliability,
        ResourceLimits,
        Benchmark,
    ]
}

pub fn d(s: &str) -> Digest {
    Digest::of_bytes(s.as_bytes())
}

pub fn challenge_def(tier: Tier, name: &str) -> ChallengeDefinition {
    ChallengeDefinition {
        schema: "arena-challenge-v1".into(),
        name: name.into(),
        season: "test".into(),
        tier,
        nearcore: NearcorePin {
            repo: "https://github.com/near/nearcore".into(),
            tag: "2.13.4".into(),
            commit: "0".repeat(40),
        },
        protocol_version: 77,
        chain_id: "testnet".into(),
        runtime_config_digest: d("runtime"),
        semantic_scope: SemanticScope {
            name: "transfer-v1".into(),
            kind: ScopeKind::Subset,
            granularity: "single_action_receipt_transition".into(),
            restrictions: vec![],
            excludes: vec!["block_finality".into()],
            formal_spec: FormalSpecRef {
                relation_module: "NearSpec.TransferV1".into(),
                relation_decl: "NearSpec.TransferV1.NearRelation".into(),
                tree_digest: d("spec"),
                lean_toolchain: "leanprover/lean4:v4.0.0".into(),
            },
            spec_doc_digest: d("doc"),
        },
        claim_encoding: ClaimEncoding {
            format: "near-arena-claim-v1".into(),
            spec_digest: d("claim"),
            max_request_bytes: 1 << 20,
            max_witness_bytes: 1 << 24,
            max_claim_bytes: 1 << 16,
        },
        security_profile: SecurityProfile {
            id: "validity-classical-128".into(),
            privacy: Privacy::ValidityOnly,
            adversary: AdversaryClass::Classical,
            target_bits: 128,
            model: SecurityModel::RandomOracle,
            setup_model: SetupModel::Transparent,
            allowed_assumptions: vec!["sha256-cr".into(), "rom".into()],
            max_prover_queries_log2: 40,
            max_hash_queries_log2: 64,
            max_aggregation_depth: 1,
            deployment_proofs_log2: 30,
        },
        toolchain_policy: ToolchainPolicy {
            lean_toolchain: "leanprover/lean4:v4.0.0".into(),
            checker_image: d("checker-image-1"),
            axiom_allowlist: vec![
                "propext".into(),
                "Quot.sound".into(),
                "Classical.choice".into(),
            ],
            allowed_packages: vec![],
            recheckers: vec!["lean4checker".into()],
        },
        required_obligations: all_obligations(),
        not_applicable_gates: vec![ObligationId::FormalZk],
        hardware_profile: HardwareProfile {
            id: "cpu-32".into(),
            cpu_model: "test".into(),
            vcpus: 32,
            ram_bytes: 64 << 30,
            gpu: None,
        },
        workload_suite: WorkloadSuite {
            revision: "r1".into(),
            classes: vec![
                WorkloadClass {
                    id: "small".into(),
                    description: "s".into(),
                    weight_ppm: 600_000,
                    batch_size: 4,
                    generator: d("g1"),
                },
                WorkloadClass {
                    id: "large".into(),
                    description: "l".into(),
                    weight_ppm: 400_000,
                    batch_size: 1,
                    generator: d("g2"),
                },
            ],
            public_fixtures: d("fixtures"),
            heldout_commitment: d("heldout"),
            baseline_submission: None,
            baseline_ns: vec![("small".into(), 1_000_000), ("large".into(), 4_000_000)],
        },
        measurement: MeasurementProcedure {
            warmup_runs: 1,
            measured_runs: 5,
            aggregation: "median".into(),
            outlier_mad_k: 5,
            cold_runs: 1,
            concurrency: 1,
            per_run_timeout_ms: 60_000,
        },
        resource_limits: ResourceLimits {
            max_proof_bytes: 1 << 20,
            max_verify_ms: 1000,
            max_prove_ms: 600_000,
            max_ram_bytes: 16 << 30,
            max_vram_bytes: 0,
            max_public_artifact_bytes: 1 << 30,
            max_prepare_ms: 600_000,
            max_build_ms: 3_600_000,
        },
        supersedes: None,
        created_at: "2026-10-01T00:00:00Z".into(),
    }
}

impl TestApp {
    pub fn url(&self, p: &str) -> String {
        format!("{}{p}", self.base)
    }

    pub fn sign(&self, def: &ChallengeDefinition) -> String {
        hex::encode(
            self.gov
                .sign(&arena_types::canonical_json(def).unwrap())
                .to_bytes(),
        )
    }

    /// Register a challenge through the admin API; returns its id.
    pub async fn register(&self, def: &ChallengeDefinition) -> String {
        let r = self
            .http
            .post(self.url("/v1/admin/challenges"))
            .bearer_auth(&self.admin_token)
            .json(&json!({"definition": def, "signature": self.sign(def)}))
            .send()
            .await
            .unwrap();
        assert!(
            r.status().is_success(),
            "register: {}",
            r.text().await.unwrap()
        );
        r.json::<Value>().await.unwrap()["id"]
            .as_str()
            .unwrap()
            .to_string()
    }

    pub async fn upload(&self, token: &str, bytes: &[u8]) -> reqwest::Response {
        self.http
            .post(self.url("/v1/uploads"))
            .bearer_auth(token)
            .body(bytes.to_vec())
            .send()
            .await
            .unwrap()
    }

    pub async fn submit_raw(&self, token: &str, body: Value) -> reqwest::Response {
        self.http
            .post(self.url("/v1/submissions"))
            .bearer_auth(token)
            .json(&body)
            .send()
            .await
            .unwrap()
    }

    /// Upload `package` and submit it; returns the submission view.
    pub async fn submit(
        &self,
        chal: &str,
        package: &[u8],
        key: &str,
        parent: Option<&str>,
    ) -> SubmissionView {
        let up = self.upload(&self.agent_token, package).await;
        assert_eq!(up.status(), 201, "upload: {}", up.text().await.unwrap());
        let up: Value = up.json().await.unwrap();
        let r = self
            .submit_raw(
                &self.agent_token,
                json!({"challenge_id": chal, "upload_digest": up["digest"], "idempotency_key": key, "parent": parent}),
            )
            .await;
        assert_eq!(r.status(), 201, "submit: {}", r.text().await.unwrap());
        r.json().await.unwrap()
    }

    pub async fn view(&self, id: &str) -> SubmissionView {
        let r = self
            .http
            .get(self.url(&format!("/v1/submissions/{id}")))
            .send()
            .await
            .unwrap();
        assert_eq!(r.status(), 200);
        r.json().await.unwrap()
    }

    pub async fn get_json(&self, path: &str) -> (u16, Value) {
        let r = self.http.get(self.url(path)).send().await.unwrap();
        let s = r.status().as_u16();
        (s, r.json().await.unwrap_or(Value::Null))
    }

    pub async fn admin_post(&self, path: &str, body: Value) -> (u16, Value) {
        let r = self
            .http
            .post(self.url(path))
            .bearer_auth(&self.admin_token)
            .json(&body)
            .send()
            .await
            .unwrap();
        let s = r.status().as_u16();
        (s, r.json().await.unwrap_or(Value::Null))
    }

    pub fn fake_worker(&self) -> fake_worker::FakeWorker {
        fake_worker::FakeWorker::new(&self.worker_base, &self.worker_token)
    }

    pub async fn job_states(&self, sub: &str) -> Vec<(String, String, i32)> {
        sqlx::query_as("SELECT kind, state, attempt FROM jobs WHERE submission_id = $1 ORDER BY created_at, kind")
            .bind(sub)
            .fetch_all(&self.pool)
            .await
            .unwrap()
    }
}
