//! Security / integrity properties: audit immutability, revocation, ranking
//! rules, quotas and rate limits, tier caps for dev sandboxes, report-key
//! isolation from workers, challenge signature checks, DB role grants.

mod common;

use arena_db::sqlx;
use arena_jobs::*;
use arena_orchestrator::signer::ReportSigner;
use arena_types::challenge::Tier;
use arena_types::*;
use common::*;
use serde_json::{json, Value};

#[tokio::test]
async fn audit_log_and_records_are_immutable() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-immut")).await;
    let v = app.submit(&chal, b"pkg", "k", None).await;
    app.fake_worker().drain().await;
    let p = &app.pool;
    for stmt in [
        "UPDATE audit_events SET action = 'x'",
        "DELETE FROM audit_events",
        "TRUNCATE audit_events",
        "UPDATE submissions SET package_digest = package_digest",
        "DELETE FROM submissions",
        "DELETE FROM gate_results",
        "UPDATE gate_results SET status = 'PASS'",
        "UPDATE runs SET score_milli = 1",
        "DELETE FROM runs",
        "DELETE FROM reports",
        "UPDATE reports SET signature = signature",
        "UPDATE challenges SET definition = '{}'::jsonb",
        "DELETE FROM challenges",
        "DELETE FROM formal_cache",
    ] {
        let e = sqlx::query(stmt).execute(p).await;
        assert!(e.is_err(), "{stmt} must be rejected");
    }
    let (n,): (i64,) = sqlx::query_as("SELECT count(*) FROM audit_events WHERE submission_id = $1")
        .bind(&v.id)
        .fetch_one(p)
        .await
        .unwrap();
    assert!(n > 20);
    // only `open` may change on a challenge
    sqlx::query("UPDATE challenges SET open = false")
        .execute(p)
        .await
        .unwrap();
}

#[tokio::test]
async fn revocation_hides_rank_but_preserves_history() {
    let app = spawn().await;
    let chal = app
        .register(&challenge_def(Tier::Demo, "demo-revoke"))
        .await;
    let v = app.submit(&chal, b"pkg", "k", None).await;
    app.fake_worker().drain().await;
    let (s, r) = app
        .admin_post(
            &format!("/v1/admin/submissions/{}/revoke", v.id),
            json!({"reason": "benchmark host misconfigured\u{0007}"}),
        )
        .await;
    assert_eq!(s, 201, "{r}");
    assert_eq!(r["reason"], "benchmark host misconfigured");
    let (s, _) = app
        .admin_post(
            &format!("/v1/admin/submissions/{}/revoke", v.id),
            json!({"reason": "again"}),
        )
        .await;
    assert_eq!(s, 409);
    let (s, _) = app
        .admin_post(
            &format!("/v1/admin/submissions/{}/revoke", v.id),
            json!({"reason": "  "}),
        )
        .await;
    assert_eq!(s, 400);
    let view = app.view(&v.id).await;
    assert_eq!(
        view.revoked.as_ref().unwrap().reason,
        "benchmark host misconfigured"
    );
    assert_eq!(view.revocation_history.len(), 1);
    assert_eq!(view.decision, Some(Decision::Admitted), "history preserved");
    assert_eq!(view.gates.len(), all_obligations().len());
    let (_, lb) = app.get_json(&format!("/v1/leaderboards/{chal}")).await;
    assert_eq!(lb[0]["revoked"], true);
    assert_eq!(lb[0]["rank"], Value::Null);
    let (_, rep) = app
        .get_json(&format!("/v1/submissions/{}/report", v.id))
        .await;
    assert_eq!(rep["revocation"]["reason"], "benchmark host misconfigured");
    arena_orchestrator::report::verify(&serde_json::from_value(rep).unwrap()).unwrap();
    // agents cannot revoke
    let r = app
        .http
        .post(app.url(&format!("/v1/admin/submissions/{}/revoke", v.id)))
        .bearer_auth(&app.agent_token)
        .json(&json!({"reason": "x"}))
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 401);
}

/// Insert a decided run directly (test fixture; bypasses the pipeline) to
/// exercise the ranking rules over tiers/decisions/revocations.
#[allow(clippy::too_many_arguments)]
async fn fixture(
    app: &TestApp,
    chal: &str,
    key: &str,
    challenge_tier: &str,
    tier: &str,
    decision: &str,
    accepted: bool,
    score: Option<i64>,
) -> String {
    let p = &app.pool;
    let (agent_id,): (String,) = sqlx::query_as("SELECT id FROM agents WHERE handle = 'alice'")
        .fetch_one(p)
        .await
        .unwrap();
    let digest = Digest::of_bytes(key.as_bytes());
    let upl = arena_db::new_id("upl");
    sqlx::query("INSERT INTO uploads (id, agent_id, digest, size_bytes) VALUES ($1, $2, $3, 1)")
        .bind(&upl)
        .bind(&agent_id)
        .bind(digest.as_str())
        .execute(p)
        .await
        .unwrap();
    let sub = arena_db::new_id("sub");
    sqlx::query(
        "INSERT INTO submissions (id, agent_id, challenge_id, package_digest, upload_id, idempotency_key, request_digest)
         VALUES ($1, $2, $3, $4, $5, $6, 'fixture')",
    )
    .bind(&sub)
    .bind(&agent_id)
    .bind(chal)
    .bind(digest.as_str())
    .bind(&upl)
    .bind(key)
    .execute(p)
    .await
    .unwrap();
    sqlx::query(
        "INSERT INTO runs (id, submission_id, run_number, trigger, requested_by, challenge_tier, tier, stage, decision,
            accepted, score_milli, candidate_name, decided_at)
         VALUES ($1, $2, 1, 'fixture', 'test', $3, $4, 'DECIDED', $5, $6, $7, $8, now())",
    )
    .bind(arena_db::new_id("run"))
    .bind(&sub)
    .bind(challenge_tier)
    .bind(tier)
    .bind(decision)
    .bind(accepted)
    .bind(score)
    .bind(key)
    .execute(p)
    .await
    .unwrap();
    sub
}

#[tokio::test]
async fn ranking_rules_formal_only_admitted_not_revoked() {
    let app = spawn().await;
    let formal = app
        .register(&challenge_def(Tier::Formal, "formal-board"))
        .await;
    let f150 = fixture(
        &app,
        &formal,
        "f150",
        "formal",
        "formal",
        "ADMITTED",
        true,
        Some(150_000),
    )
    .await;
    let f250 = fixture(
        &app,
        &formal,
        "f250",
        "formal",
        "formal",
        "ADMITTED",
        true,
        Some(250_000),
    )
    .await;
    let capped = fixture(
        &app,
        &formal,
        "capped",
        "formal",
        "demo",
        "ADMITTED",
        true,
        Some(900_000),
    )
    .await;
    let revoked = fixture(
        &app,
        &formal,
        "revoked",
        "formal",
        "formal",
        "ADMITTED",
        true,
        Some(800_000),
    )
    .await;
    fixture(
        &app, &formal, "rejected", "formal", "formal", "REJECTED", false, None,
    )
    .await;
    fixture(
        &app,
        &formal,
        "inconcl",
        "formal",
        "formal",
        "INCONCLUSIVE",
        false,
        None,
    )
    .await;
    let (s, _) = app
        .admin_post(
            &format!("/v1/admin/submissions/{revoked}/revoke"),
            json!({"reason": "cheated"}),
        )
        .await;
    assert_eq!(s, 201);
    let (_, lb) = app.get_json(&format!("/v1/leaderboards/{formal}")).await;
    let lb: Vec<LeaderboardEntry> = serde_json::from_value(lb).unwrap();
    assert_eq!(lb.len(), 6, "all submissions listed with labels");
    let ranked: Vec<(&str, u32)> = lb
        .iter()
        .filter_map(|e| e.rank.map(|r| (e.submission_id.as_str(), r)))
        .collect();
    assert_eq!(ranked, vec![(f250.as_str(), 1), (f150.as_str(), 2)]);
    assert_eq!(lb[0].submission_id, f250);
    let capped_e = lb.iter().find(|e| e.submission_id == capped).unwrap();
    assert_eq!((capped_e.rank, capped_e.tier), (None, Tier::Demo));
    assert!(
        lb.iter()
            .find(|e| e.submission_id == revoked)
            .unwrap()
            .revoked
    );

    // non-formal challenges never rank, even when admitted with a score
    let exp = app
        .register(&challenge_def(Tier::Experimental, "exp-board"))
        .await;
    fixture(
        &app,
        &exp,
        "e1",
        "experimental",
        "experimental",
        "ADMITTED",
        true,
        Some(500_000),
    )
    .await;
    let demo = app.register(&challenge_def(Tier::Demo, "demo-board")).await;
    fixture(
        &app,
        &demo,
        "d1",
        "demo",
        "demo",
        "ADMITTED",
        true,
        Some(500_000),
    )
    .await;
    for c in [&exp, &demo] {
        let (_, lb) = app.get_json(&format!("/v1/leaderboards/{c}")).await;
        let lb: Vec<LeaderboardEntry> = serde_json::from_value(lb).unwrap();
        assert_eq!(lb.len(), 1);
        assert_eq!(lb[0].rank, None);
    }
}

#[tokio::test]
async fn demo_capped_workers_never_get_non_demo_work() {
    let app = spawn().await;
    let formal = app.register(&challenge_def(Tier::Formal, "formal-x")).await;
    let exp = app
        .register(&challenge_def(Tier::Experimental, "exp-x"))
        .await;
    let vf = app.submit(&formal, b"pkg-f", "f", None).await;
    app.submit(&exp, b"pkg-e", "e", None).await;
    // the demo-capped fake worker sees nothing
    assert!(app.fake_worker().lease(&[], None).await.is_none());
    // bwrap-dev registration is capped to demo even if formal is requested
    let (s, w) = app
        .admin_post(
            "/v1/admin/workers",
            json!({"name": "dev-box", "sandbox_backend": "bwrap-dev", "tier_cap": "formal"}),
        )
        .await;
    assert_eq!(s, 201);
    let (cap,): (i16,) = sqlx::query_as("SELECT tier_cap FROM workers WHERE name = 'dev-box'")
        .fetch_one(&app.pool)
        .await
        .unwrap();
    assert_eq!(cap, 0);
    let bw = common::fake_worker::FakeWorker::new(&app.worker_base, w["token"].as_str().unwrap());
    assert!(
        bw.lease(&[], None).await.is_none(),
        "bwrap-dev never leases non-demo jobs"
    );
    // the DB itself refuses a non-demo bwrap-dev worker
    let e = sqlx::query(
        "INSERT INTO workers (id, name, token_hash, sandbox_backend, tier_cap) VALUES ($1, 'x', $2, 'bwrap-dev', 2)",
    )
    .bind(arena_db::new_id("wrk"))
    .bind(arena_db::hash_token("t"))
    .execute(&app.pool)
    .await;
    assert!(e.is_err());

    // a formal-capable worker can lease, but a result produced via bwrap-dev is capped to demo
    let (_, fw) = app
        .admin_post(
            "/v1/admin/workers",
            json!({"name": "fc", "sandbox_backend": "firecracker", "tier_cap": "formal"}),
        )
        .await;
    let fc = common::fake_worker::FakeWorker::new(&app.worker_base, fw["token"].as_str().unwrap());
    let job = fc.lease(&[], None).await.unwrap();
    assert_eq!(job.submission_id, vf.id, "oldest job first");
    let mut result = fc.result_for(&job).await;
    result.execution = ExecutionInfo {
        sandbox_backend: "bwrap-dev".into(),
        tier_cap: Tier::Formal,
        worker_version: "x".into(),
    };
    fc.client
        .complete(
            &job.job_id,
            &CompleteRequest {
                lease_id: job.lease_id.clone(),
                result,
            },
        )
        .await
        .unwrap();
    let v = app.view(&vf.id).await;
    assert_eq!(v.tier, Tier::Demo);
    // formal challenge + demo-capped evaluation can never be ADMITTED
    fc.drain().await;
    let v = app.view(&vf.id).await;
    assert_eq!(v.decision, Some(Decision::Inconclusive));
    assert_eq!(v.accepted, Some(false));
    assert!(v.reason_codes.contains(&ReasonCode::DemoOnly));
}

#[tokio::test]
async fn quotas_and_size_limits() {
    let mut opts = Opts::default();
    opts.limits.max_upload_bytes = 64;
    let app = spawn_with(opts).await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-quota")).await;
    let r = app.upload(&app.agent_token, &[1u8; 65]).await;
    assert_eq!(r.status(), 413);
    let r = app.upload(&app.agent_token, b"").await;
    assert_eq!(r.status(), 400);
    let r = app
        .http
        .put(app.url("/v1/admin/quotas/alice"))
        .bearer_auth(&app.admin_token)
        .json(&json!({"max_submissions_per_day": 1, "max_upload_bytes_per_day": 20, "max_active_runs": 5}))
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 204);
    app.submit(&chal, b"aaaaaaaa", "q1", None).await; // 8 bytes
    let r = app.upload(&app.agent_token, b"bbbbbbbbbbbbbbb").await; // 15 more > 20
    assert_eq!(r.status(), 429);
    let up: Value = app
        .upload(&app.agent_token, b"cccc")
        .await
        .json()
        .await
        .unwrap();
    let r = app
        .submit_raw(
            &app.agent_token,
            json!({"challenge_id": chal, "upload_digest": up["digest"], "idempotency_key": "q2"}),
        )
        .await;
    assert_eq!(r.status(), 429, "daily submission quota");
    // active-run quota for bob
    let r = app
        .http
        .put(app.url("/v1/admin/quotas/bob"))
        .bearer_auth(&app.admin_token)
        .json(&json!({"max_submissions_per_day": 10, "max_upload_bytes_per_day": 1000, "max_active_runs": 1}))
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 204);
    let mut ups = vec![];
    for b in [&b"b1"[..], b"b2"] {
        let u: Value = app.upload(&app.agent2_token, b).await.json().await.unwrap();
        ups.push(u["digest"].clone());
    }
    let r = app
        .submit_raw(
            &app.agent2_token,
            json!({"challenge_id": chal, "upload_digest": ups[0], "idempotency_key": "a"}),
        )
        .await;
    assert_eq!(r.status(), 201);
    let r = app
        .submit_raw(
            &app.agent2_token,
            json!({"challenge_id": chal, "upload_digest": ups[1], "idempotency_key": "b"}),
        )
        .await;
    assert_eq!(r.status(), 429);
    app.fake_worker().drain().await;
    let r = app
        .submit_raw(
            &app.agent2_token,
            json!({"challenge_id": chal, "upload_digest": ups[1], "idempotency_key": "b"}),
        )
        .await;
    assert_eq!(r.status(), 201, "slot freed once decided");
}

#[tokio::test]
async fn per_agent_rate_limit() {
    let mut opts = Opts::default();
    opts.limits.rate_per_minute = 60;
    opts.limits.rate_burst = 2;
    let app = spawn_with(opts).await;
    assert_eq!(app.upload(&app.agent_token, b"1").await.status(), 201);
    assert_eq!(app.upload(&app.agent_token, b"2").await.status(), 201);
    let r = app.upload(&app.agent_token, b"3").await;
    assert_eq!(r.status(), 429);
    assert!(r.headers().contains_key("retry-after"));
    assert_eq!(
        app.upload(&app.agent2_token, b"4").await.status(),
        201,
        "limits are per agent"
    );
}

#[tokio::test]
async fn worker_cannot_reach_report_key_or_admin_surface() {
    let app = spawn().await;
    let signer = ReportSigner::from_hex(REPORT_SEED_HEX).unwrap();
    assert_eq!(
        signer.public_key_hex(),
        app.state.orch.report_public_key_hex()
    );
    let chal = app.register(&challenge_def(Tier::Demo, "demo-key")).await;
    let v = app.submit(&chal, b"pkg", "k", None).await;
    let w = app.fake_worker();
    // every leased job payload is free of key material
    while let Some(job) = w.lease(&[], None).await {
        let bytes = serde_json::to_vec(&job).unwrap();
        assert!(
            !signer.leaks_into(&bytes),
            "job payload leaks the report key"
        );
        let result = w.result_for(&job).await;
        w.client
            .complete(
                &job.job_id,
                &CompleteRequest {
                    lease_id: job.lease_id.clone(),
                    result,
                },
            )
            .await
            .unwrap();
    }
    assert_eq!(app.view(&v.id).await.decision, Some(Decision::Admitted));

    // no table holds key material (reports hold only the public key + signature)
    let tables: Vec<(String,)> =
        sqlx::query_as("SELECT tablename::text FROM pg_tables WHERE schemaname = 'public'")
            .fetch_all(&app.pool)
            .await
            .unwrap();
    for (t,) in tables {
        let rows: Vec<(String,)> = sqlx::query_as(&format!("SELECT to_jsonb(x)::text FROM {t} x"))
            .fetch_all(&app.pool)
            .await
            .unwrap();
        for (r,) in rows {
            assert!(
                !signer.leaks_into(r.as_bytes()),
                "table {t} leaks the report key"
            );
        }
    }
    // nor does the object store
    for e in walk(app.store_dir.path()) {
        assert!(
            !signer.leaks_into(&std::fs::read(&e).unwrap()),
            "{} leaks the report key",
            e.display()
        );
    }
    // artifact API cannot be used to fetch key bytes
    let seed = hex::decode(REPORT_SEED_HEX).unwrap();
    for probe in [
        Digest::of_bytes(&seed),
        Digest::of_bytes(REPORT_SEED_HEX.as_bytes()),
    ] {
        assert!(w.client.get_artifact(&probe).await.unwrap().is_none());
    }
    // worker token is useless on the public/admin API; admin routes do not exist on the worker listener
    for (base, path, tok) in [
        (&app.base, "/v1/admin/audit", &app.worker_token),
        (&app.worker_base, "/v1/admin/audit", &app.admin_token),
        (&app.base, "/internal/v1/jobs/lease", &app.worker_token),
    ] {
        let r = app
            .http
            .get(format!("{base}{path}"))
            .bearer_auth(tok)
            .send()
            .await
            .unwrap();
        assert!(
            matches!(r.status().as_u16(), 401 | 404 | 405),
            "{base}{path}: {}",
            r.status()
        );
    }
    let r = app
        .http
        .post(format!("{}/internal/v1/jobs/lease", app.base))
        .bearer_auth(&app.worker_token)
        .send()
        .await
        .unwrap();
    assert_eq!(
        r.status(),
        404,
        "worker API is not served on the public listener"
    );
    let r = app
        .http
        .post(format!("{}/internal/v1/jobs/lease", app.worker_base))
        .bearer_auth(&app.agent_token)
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 401, "agent tokens are not worker tokens");
    let r = app
        .http
        .get(format!("{}/v1/challenges", app.worker_base))
        .send()
        .await
        .unwrap();
    assert_eq!(
        r.status(),
        404,
        "public API is not served on the worker listener"
    );
}

fn walk(p: &std::path::Path) -> Vec<std::path::PathBuf> {
    let mut out = vec![];
    for e in std::fs::read_dir(p).unwrap().flatten() {
        let path = e.path();
        if path.is_dir() {
            out.extend(walk(&path));
        } else {
            out.push(path);
        }
    }
    out
}

#[tokio::test]
async fn challenge_registration_requires_governance_signature() {
    let app = spawn().await;
    let def = challenge_def(Tier::Demo, "demo-sig");
    let good = app.sign(&def);
    // wrong key
    let other = ed25519_dalek::SigningKey::from_bytes(&[9u8; 32]);
    use ed25519_dalek::Signer;
    let bad = hex::encode(other.sign(&canonical_json(&def).unwrap()).to_bytes());
    let (s, e) = app
        .admin_post(
            "/v1/admin/challenges",
            json!({"definition": def, "signature": bad}),
        )
        .await;
    assert_eq!(s, 400, "{e}");
    // tampered definition with the original signature
    let mut t = def.clone();
    t.protocol_version += 1;
    let (s, _) = app
        .admin_post(
            "/v1/admin/challenges",
            json!({"definition": t, "signature": good}),
        )
        .await;
    assert_eq!(s, 400);
    // garbage signature
    let (s, _) = app
        .admin_post(
            "/v1/admin/challenges",
            json!({"definition": def, "signature": "zz"}),
        )
        .await;
    assert_eq!(s, 400);
    // unknown fields are rejected (no unsigned extras)
    let mut raw = serde_json::to_value(&def).unwrap();
    raw["security_bits"] = json!(128);
    let (s, _) = app
        .admin_post(
            "/v1/admin/challenges",
            json!({"definition": raw, "signature": good}),
        )
        .await;
    assert_eq!(s, 422);
    // agents cannot register
    let r = app
        .http
        .post(app.url("/v1/admin/challenges"))
        .bearer_auth(&app.agent_token)
        .json(&json!({"definition": def, "signature": good}))
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 401);
    // good (base64 accepted too); id recomputed; idempotent re-registration
    use base64::Engine;
    let b64 = base64::engine::general_purpose::STANDARD.encode(hex::decode(&good).unwrap());
    let (s, r) = app
        .admin_post(
            "/v1/admin/challenges",
            json!({"definition": def, "signature": b64}),
        )
        .await;
    assert_eq!(s, 201);
    assert_eq!(r["id"], json!(def.id().unwrap()));
    let (s, r) = app
        .admin_post(
            "/v1/admin/challenges",
            json!({"definition": def, "signature": good}),
        )
        .await;
    assert_eq!((s, r["created"].clone()), (200, json!(false)));
    // closing a challenge stops submissions
    let (s, _) = app
        .admin_post(
            &format!("/v1/admin/challenges/{}/status", def.id().unwrap()),
            json!({"open": false}),
        )
        .await;
    assert_eq!(s, 204);
    let up: Value = app
        .upload(&app.agent_token, b"p")
        .await
        .json()
        .await
        .unwrap();
    let r = app
        .submit_raw(&app.agent_token, json!({"challenge_id": def.id().unwrap(), "upload_digest": up["digest"], "idempotency_key": "x"}))
        .await;
    assert_eq!(r.status(), 409);
    // unknown challenge
    let (s, _) = app
        .get_json("/v1/challenges/chl_00000000000000000000000000000000")
        .await;
    assert_eq!(s, 404);
}

#[tokio::test]
async fn challenges_dir_bootstrap_refuses_bad_files() {
    let app = spawn().await;
    let dir = tempfile::tempdir().unwrap();
    let good = challenge_def(Tier::Demo, "dir-good");
    let id = good.id().unwrap();
    std::fs::write(
        dir.path().join(format!("{id}.json")),
        serde_json::to_string_pretty(&good).unwrap(),
    )
    .unwrap();
    std::fs::write(dir.path().join(format!("{id}.sig")), app.sign(&good)).unwrap();
    // misnamed file (id mismatch)
    let other = challenge_def(Tier::Demo, "dir-other");
    std::fs::write(
        dir.path().join("chl_0123456789abcdef0123456789abcdef.json"),
        serde_json::to_string(&other).unwrap(),
    )
    .unwrap();
    std::fs::write(
        dir.path().join("chl_0123456789abcdef0123456789abcdef.sig"),
        app.sign(&other),
    )
    .unwrap();
    // bad signature
    let bad = challenge_def(Tier::Demo, "dir-bad");
    let bid = bad.id().unwrap();
    std::fs::write(
        dir.path().join(format!("{bid}.json")),
        serde_json::to_string(&bad).unwrap(),
    )
    .unwrap();
    std::fs::write(dir.path().join(format!("{bid}.sig")), app.sign(&good)).unwrap();
    let keys = app.state.orch.governance_keys().to_vec();
    let (ok, refused) = arena_server::bootstrap::challenges_from_dir(
        &app.pool,
        dir.path(),
        &keys,
        &Default::default(),
    )
    .await
    .unwrap();
    assert_eq!((ok, refused), (1, 2));
    let (_, list) = app.get_json("/v1/challenges").await;
    assert_eq!(list.as_array().unwrap().len(), 1);
    assert_eq!(list[0]["id"], json!(id));
}

#[tokio::test]
async fn least_privilege_roles() {
    let app = spawn().await;
    let sfx = &uuid::Uuid::new_v4().simple().to_string()[..8];
    let names = [
        format!("arena_server_test_api_{sfx}"),
        format!("arena_server_test_wrk_{sfx}"),
        format!("arena_server_test_adm_{sfx}"),
    ];
    let p = &app.pool;
    for n in &names {
        if let Err(e) = sqlx::query(&format!("CREATE ROLE {n} NOLOGIN"))
            .execute(p)
            .await
        {
            eprintln!("SKIP least_privilege_roles: cannot create roles on the shared server ({e})");
            return;
        }
    }
    let roles = arena_db::roles::RoleNames {
        api: &names[0],
        worker: &names[1],
        admin: &names[2],
    };
    let result: Result<(), String> = async {
        sqlx::raw_sql(&arena_db::roles::grants_sql(roles))
            .execute(p)
            .await
            .map_err(|e| e.to_string())?;
        for n in &names {
            sqlx::query(&format!("GRANT {n} TO CURRENT_USER"))
                .execute(p)
                .await
                .map_err(|e| e.to_string())?;
        }
        // (role, statement, allowed?)
        let cases: Vec<(&str, &str, bool)> = vec![
            (&names[0], "SELECT count(*) FROM submissions", true),
            (&names[0], "SELECT count(*) FROM admins", false),
            (&names[0], "SELECT count(*) FROM workers", false),
            (&names[0], "SELECT count(*) FROM formal_cache", false),
            (&names[0], "INSERT INTO challenges (id) VALUES ('x')", false),
            (&names[0], "DELETE FROM uploads", false),
            (
                &names[0],
                "INSERT INTO revocations (submission_id, reason, revoked_by) VALUES ('x','y','z')",
                false,
            ),
            (&names[1], "SELECT count(*) FROM jobs", true),
            (&names[1], "SELECT count(*) FROM admins", false),
            (&names[1], "SELECT count(*) FROM quotas", false),
            (&names[1], "UPDATE challenges SET open = true", false),
            (&names[1], "DELETE FROM jobs", false),
            (&names[2], "SELECT count(*) FROM admins", true),
            (&names[2], "DELETE FROM agents", false),
            (&names[2], "TRUNCATE audit_events", false),
        ];
        for (role, stmt, allowed) in cases {
            let mut tx = p.begin().await.map_err(|e| e.to_string())?;
            sqlx::query(&format!("SET LOCAL ROLE {role}"))
                .execute(&mut *tx)
                .await
                .map_err(|e| e.to_string())?;
            let res = sqlx::query(stmt).execute(&mut *tx).await;
            let denied = matches!(&res, Err(e) if e.to_string().contains("permission denied"));
            tx.rollback().await.ok();
            if allowed && res.is_err() {
                return Err(format!("{role}: `{stmt}` should be allowed: {res:?}"));
            }
            if !allowed && !denied {
                return Err(format!(
                    "{role}: `{stmt}` should be denied by privileges, got {res:?}"
                ));
            }
        }
        Ok(())
    }
    .await;
    for n in &names {
        let _ = sqlx::query(&format!("DROP OWNED BY {n}")).execute(p).await;
        let _ = sqlx::query(&format!("DROP ROLE {n}")).execute(p).await;
    }
    result.unwrap();
}

/// The full pipeline (submit, lease, complete, cache, cancel, revoke, rerun,
/// reports, leaderboard) works when each component uses its least-privilege role.
#[tokio::test]
async fn full_pipeline_under_split_least_privilege_roles() {
    scenario_under_roles(false).await;
}

/// Same, with the single-role grants used by deploy/sql/grants.sql.
#[tokio::test]
async fn full_pipeline_under_single_deployment_role() {
    scenario_under_roles(true).await;
}

async fn scenario_under_roles(single_role: bool) {
    let app = spawn_with(Opts {
        split_roles: true,
        single_role,
        ..Default::default()
    })
    .await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-roles")).await;
    let a = app.submit(&chal, b"pkg-a", "a", None).await;
    app.fake_worker().drain().await;
    assert_eq!(app.view(&a.id).await.decision, Some(Decision::Admitted));
    let b = app.submit(&chal, b"pkg-b", "b", Some(&a.id)).await;
    app.fake_worker().drain().await;
    let b = app.view(&b.id).await;
    assert!(
        b.gates.iter().any(|g| g.reused_from.is_some()),
        "cache reuse under worker role"
    );
    let c = app.submit(&chal, b"pkg-c", "c", None).await;
    let r = app
        .http
        .post(app.url(&format!("/v1/submissions/{}/cancel", c.id)))
        .bearer_auth(&app.agent_token)
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 200);
    let (s, _) = app
        .admin_post(
            &format!("/v1/admin/submissions/{}/revoke", a.id),
            json!({"reason": "test"}),
        )
        .await;
    assert_eq!(s, 201);
    let (s, _) = app
        .admin_post(
            &format!("/v1/admin/submissions/{}/rerun", a.id),
            json!({"reason": "test"}),
        )
        .await;
    assert_eq!(s, 201);
    let mut w = app.fake_worker();
    w.behavior.infra_fail = Some(JobKind::Validate);
    w.drain().await;
    assert_eq!(app.view(&a.id).await.decision, Some(Decision::InfraError));
    let (s, _) = app
        .admin_post(
            "/v1/admin/formal-cache/invalidate",
            json!({"assumption": "rom", "reason": "t"}),
        )
        .await;
    assert_eq!(s, 200);
    let (s, _) = app.get_json(&format!("/v1/leaderboards/{chal}")).await;
    assert_eq!(s, 200);
    let (s, _) = app
        .get_json(&format!("/v1/submissions/{}/report", b.id))
        .await;
    assert_eq!(s, 200);
    let r = app
        .http
        .get(app.url("/v1/admin/audit"))
        .bearer_auth(&app.admin_token)
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 200);
    let r = app
        .http
        .put(app.url("/v1/admin/quotas/alice"))
        .bearer_auth(&app.admin_token)
        .json(&json!({"max_submissions_per_day": 1, "max_upload_bytes_per_day": 1, "max_active_runs": 1}))
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 204);
    assert_eq!(
        app.state
            .orch
            .reap_expired(&app.state.worker_db)
            .await
            .unwrap(),
        0
    );
}

/// The governance lane's checked-in challenges load under its dev key and the
/// governed `security/` policy (same rules as `tools/arena-admin`).
#[tokio::test]
async fn repo_challenges_load_with_governance_policy() {
    let app = spawn().await;
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let text = std::fs::read_to_string(root.join("challenges/governance-dev.pub")).unwrap();
    let keys = arena_server::config::parse_pubkeys_text(&text).unwrap();
    assert_eq!(keys.len(), 1);
    assert!(keys[0].1, "the repo dev key is flagged dev_only");
    // the local operator key (signs the formal NEAR challenge) is not dev-only
    let text = std::fs::read_to_string(root.join("challenges/governance-local.pub")).unwrap();
    let local = arena_server::config::parse_pubkeys_text(&text).unwrap();
    assert_eq!(local.len(), 1);
    assert!(!local[0].1, "the local operator key is not dev_only");
    let gov = arena_server::Governance {
        dev_only_keys: vec![keys[0].0],
        governed: Some(arena_admin::GovernedSet::load(&root.join("security")).unwrap()),
    };
    let (ok, refused) = arena_server::bootstrap::challenges_from_dir(
        &app.pool,
        &root.join("challenges"),
        &[keys[0].0, local[0].0],
        &gov,
    )
    .await
    .unwrap();
    assert!(ok >= 2, "repo challenges (demo + formal) not loaded");
    assert_eq!(refused, 0);
    // a formal challenge signed by a dev-only key is refused
    let def = challenge_def(Tier::Formal, "formal-devkey");
    let sig = arena_db::challenge::parse_signature(&app.sign(&def)).unwrap();
    let v = arena_db::challenge::verify_definition(def, &sig, &[app.gov.verifying_key()]).unwrap();
    let dev_gov = arena_server::Governance {
        dev_only_keys: vec![app.gov.verifying_key()],
        governed: None,
    };
    assert!(dev_gov.check(&v).unwrap_err().contains("dev-only"));
    // and governance policy rejects definitions that violate it (fixture uses a non-governed schema id)
    let mut bad = challenge_def(Tier::Demo, "demo-policy");
    bad.toolchain_policy.axiom_allowlist.push("sorryAx".into());
    let sig = arena_db::challenge::parse_signature(&app.sign(&bad)).unwrap();
    let v = arena_db::challenge::verify_definition(bad, &sig, &[app.gov.verifying_key()]).unwrap();
    assert!(gov.check(&v).is_err());
}

/// Red-team RT-06: the daily upload-byte quota was checked before streaming
/// and not serialized, so N concurrent uploads could each use the full
/// remaining quota.
#[tokio::test]
async fn redteam_concurrent_uploads_respect_byte_quota() {
    let app = spawn().await;
    let r = app
        .http
        .put(app.url("/v1/admin/quotas/alice"))
        .bearer_auth(&app.admin_token)
        .json(&json!({"max_submissions_per_day": 10, "max_upload_bytes_per_day": 100, "max_active_runs": 5}))
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 204);
    let futs = (0..8u8).map(|i| {
        let body = vec![i; 60];
        let app = &app;
        async move { app.upload(&app.agent_token, &body).await.status().as_u16() }
    });
    let codes = futures::future::join_all(futs).await;
    let ok = codes.iter().filter(|c| **c == 201).count();
    assert_eq!(
        ok, 1,
        "only one 60-byte upload fits a 100-byte daily quota: {codes:?}"
    );
    let (used,): (i64,) = arena_db::sqlx::query_as(
        "SELECT COALESCE(SUM(size_bytes),0)::bigint FROM uploads u JOIN agents a ON a.id = u.agent_id WHERE a.handle = 'alice'",
    )
    .fetch_one(&app.pool)
    .await
    .unwrap();
    assert!(used <= 100, "{used}");
}
