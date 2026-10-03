//! Protocol-upgrade governance at the server (docs/PROTOCOL_UPGRADES.md):
//! challenge B supersedes challenge A (here the real historical boundary
//! nearcore 2.12.0 / PV 84 -> 2.13.4 / PV 86; the definitions are test
//! fixtures, not the signed challenges in `challenges/`).
//!
//! * A's results, rankings and reports are unchanged by B's registration and
//!   are labelled with A's id, A's protocol version and `superseded_by = B`;
//! * A's and B's boards are never merged;
//! * registering B closes A for new submissions (submissions get 409 naming B),
//!   A cannot be reopened, in-flight A submissions finish under A;
//! * a historical challenge loaded after its successor is inserted closed;
//! * revocations still apply to historical results.

mod common;

use arena_db::sqlx;
use arena_types::challenge::Tier;
use arena_types::*;
use common::*;
use serde_json::{json, Value};

fn pv84() -> ChallengeDefinition {
    let mut a = challenge_def(Tier::Formal, "near-transfer-receipt-pv84");
    a.nearcore.tag = "2.12.0".into();
    a.nearcore.commit = "1144e310f7e70734453167cb07f8cccf28987eb8".into();
    a.protocol_version = 84;
    a.created_at = "2026-09-01T00:00:00Z".into();
    a
}

fn pv86(supersedes: &str) -> ChallengeDefinition {
    let mut b = challenge_def(Tier::Formal, "near-transfer-receipt-pv86");
    b.nearcore.tag = "2.13.4".into();
    b.nearcore.commit = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993".into();
    b.protocol_version = 86;
    b.runtime_config_digest = d("runtime-pv86");
    b.supersedes = Some(supersedes.to_string());
    b.created_at = "2026-10-01T00:00:00Z".into();
    b
}

/// A decided formal-tier run inserted directly (the fake worker is DEMO-only,
/// so formal rankings need fixtures; same approach as tests/security.rs).
async fn formal_fixture(app: &TestApp, chal: &str, key: &str, score: i64) -> String {
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
         VALUES ($1, $2, 1, 'fixture', 'test', 'formal', 'formal', 'DECIDED', 'ADMITTED', true, $3, $4, now())",
    )
    .bind(arena_db::new_id("run"))
    .bind(&sub)
    .bind(score)
    .bind(key)
    .execute(p)
    .await
    .unwrap();
    sub
}

/// A worker allowed to lease formal-tier jobs; its (fake) results are still
/// DEMO-capped, so its runs decide but never rank.
async fn formal_capable_worker(app: &TestApp) -> common::fake_worker::FakeWorker {
    let (s, w) = app
        .admin_post(
            "/v1/admin/workers",
            json!({"name": "fc", "sandbox_backend": "firecracker", "tier_cap": "formal"}),
        )
        .await;
    assert_eq!(s, 201);
    common::fake_worker::FakeWorker::new(&app.worker_base, w["token"].as_str().unwrap())
}

async fn board(app: &TestApp, chal: &str) -> Vec<LeaderboardEntry> {
    let (s, lb) = app.get_json(&format!("/v1/leaderboards/{chal}")).await;
    assert_eq!(s, 200);
    serde_json::from_value(lb).unwrap()
}

/// Everything about an entry except the supersession label.
fn unlabelled(lb: &[LeaderboardEntry]) -> Vec<LeaderboardEntry> {
    lb.iter()
        .cloned()
        .map(|mut e| {
            e.superseded_by = None;
            e
        })
        .collect()
}

async fn submit_status(app: &TestApp, chal: &str, pkg: &[u8], key: &str) -> (u16, Value) {
    let up = app.upload(&app.agent_token, pkg).await;
    assert_eq!(up.status(), 201);
    let up: Value = up.json().await.unwrap();
    let r = app
        .submit_raw(
            &app.agent_token,
            json!({"challenge_id": chal, "upload_digest": up["digest"], "idempotency_key": key}),
        )
        .await;
    let s = r.status().as_u16();
    (s, r.json().await.unwrap_or(Value::Null))
}

#[tokio::test]
async fn superseding_keeps_history_labelled_closed_and_separate() {
    let app = spawn().await;
    let a = app.register(&pv84()).await;

    // history on A: one full (fake-worker, DEMO) pipeline run and two ranked formal results
    let worker = formal_capable_worker(&app).await;
    let demo = app.submit(&a, b"pv84-package", "a-demo", None).await;
    worker.drain().await;
    assert_eq!(app.view(&demo.id).await.stage, Stage::Decided);
    let a150 = formal_fixture(&app, &a, "a150", 150_000).await;
    let a250 = formal_fixture(&app, &a, "a250", 250_000).await;
    // an A submission still in flight when B is registered
    let inflight = app.submit(&a, b"pv84-late", "a-inflight", None).await;

    let before = board(&app, &a).await;
    assert_eq!(before.len(), 4);
    let ranked: Vec<_> = before
        .iter()
        .filter_map(|e| e.rank.map(|r| (e.submission_id.clone(), r)))
        .collect();
    assert_eq!(ranked, vec![(a250.clone(), 1), (a150.clone(), 2)]);
    for e in &before {
        assert_eq!(
            (
                e.challenge_id.as_str(),
                e.protocol_version,
                e.superseded_by.as_deref()
            ),
            (a.as_str(), 84, None)
        );
    }
    let (_, rep_before) = app
        .get_json(&format!("/v1/submissions/{}/report", demo.id))
        .await;
    let (_, ca) = app.get_json(&format!("/v1/challenges/{a}")).await;
    assert_eq!(
        (ca["open"].clone(), ca["superseded_by"].clone()),
        (json!(true), Value::Null)
    );

    // governance registers the PV86 successor
    let b = app.register(&pv86(&a)).await;
    assert_ne!(a, b);

    let (_, ca) = app.get_json(&format!("/v1/challenges/{a}")).await;
    assert_eq!(
        ca["open"],
        json!(false),
        "predecessor closed for new submissions"
    );
    assert_eq!(ca["superseded_by"], json!(b));
    assert_eq!(
        ca["definition"]["protocol_version"],
        json!(84),
        "definition untouched"
    );
    let (_, cb) = app.get_json(&format!("/v1/challenges/{b}")).await;
    assert_eq!(
        (cb["open"].clone(), cb["superseded_by"].clone()),
        (json!(true), Value::Null)
    );
    assert_eq!(cb["definition"]["supersedes"], json!(a));

    // the in-flight A submission finishes under A
    worker.drain().await;
    let v = app.view(&inflight.id).await;
    assert_eq!(
        (v.stage, v.challenge_id.as_str()),
        (Stage::Decided, a.as_str())
    );

    // A's board: same results, same ranks, now labelled
    let after = board(&app, &a).await;
    // (the in-flight entry legitimately changed: it was decided meanwhile)
    let mut x = unlabelled(
        &after
            .iter()
            .filter(|e| e.submission_id != inflight.id)
            .cloned()
            .collect::<Vec<_>>(),
    );
    let mut y: Vec<LeaderboardEntry> = before
        .iter()
        .filter(|e| e.submission_id != inflight.id)
        .cloned()
        .collect();
    assert_eq!(x.len(), 3);
    x.sort_by(|p, q| p.submission_id.cmp(&q.submission_id));
    y.sort_by(|p, q| p.submission_id.cmp(&q.submission_id));
    assert_eq!(
        after
            .iter()
            .filter(|e| e.rank.is_some())
            .map(|e| (&e.submission_id, e.rank))
            .collect::<Vec<_>>(),
        vec![(&a250, Some(1)), (&a150, Some(2))]
    );
    assert_eq!(
        x, y,
        "superseding never re-scores, re-ranks or drops historical results"
    );
    for e in &after {
        assert_eq!(
            (e.challenge_id.as_str(), e.protocol_version),
            (a.as_str(), 84)
        );
        assert_eq!(e.superseded_by.as_deref(), Some(b.as_str()));
    }
    let (_, rep_after) = app
        .get_json(&format!("/v1/submissions/{}/report", demo.id))
        .await;
    assert_eq!(rep_before, rep_after, "signed reports are immutable");

    // B's board starts empty and never shows A's results
    assert!(board(&app, &b).await.is_empty());
    let b120 = formal_fixture(&app, &b, "b120", 120_000).await;
    let bb = board(&app, &b).await;
    assert_eq!(bb.len(), 1);
    assert_eq!(
        (
            bb[0].submission_id.as_str(),
            bb[0].rank,
            bb[0].protocol_version
        ),
        (b120.as_str(), Some(1), 86)
    );
    assert_eq!(bb[0].superseded_by, None);
    let a_ids: Vec<_> = board(&app, &a)
        .await
        .into_iter()
        .map(|e| e.submission_id)
        .collect();
    assert!(!a_ids.contains(&b120), "boards are never merged");
    assert!(a_ids.contains(&a250) && a_ids.contains(&a150));

    // new submissions to A are refused and point at B; B accepts them
    let (s, err) = submit_status(&app, &a, b"pv84-after", "a-after").await;
    assert_eq!(s, 409, "{err}");
    assert_eq!(err["error"]["code"], json!("challenge_closed"), "{err}");
    assert!(err.to_string().contains(&b), "{err}");
    let (s, _) = submit_status(&app, &b, b"pv86-pkg", "b-1").await;
    assert_eq!(s, 201);

    // a superseded challenge cannot be reopened; closing/opening B still works
    let (s, err) = app
        .admin_post(
            &format!("/v1/admin/challenges/{a}/status"),
            json!({"open": true}),
        )
        .await;
    assert_eq!(s, 409, "{err}");
    assert_eq!(err["error"]["code"], json!("challenge_superseded"));
    let (s, _) = app
        .admin_post(
            &format!("/v1/admin/challenges/{a}/status"),
            json!({"open": false}),
        )
        .await;
    assert_eq!(s, 204);

    // revocations still apply to historical results, only on A's board
    let (s, _) = app
        .admin_post(
            &format!("/v1/admin/submissions/{a250}/revoke"),
            json!({"reason": "spec bug also affects PV84"}),
        )
        .await;
    assert_eq!(s, 201);
    let lb = board(&app, &a).await;
    let ranked: Vec<_> = lb
        .iter()
        .filter_map(|e| e.rank.map(|r| (e.submission_id.clone(), r)))
        .collect();
    assert_eq!(ranked, vec![(a150.clone(), 1)]);
    assert!(lb.iter().find(|e| e.submission_id == a250).unwrap().revoked);
    assert_eq!(
        board(&app, &b)
            .await
            .iter()
            .filter(|e| e.rank.is_some())
            .count(),
        1
    );

    // audit trail records the supersession
    let r = app
        .http
        .get(app.url("/v1/admin/audit"))
        .bearer_auth(&app.admin_token)
        .send()
        .await
        .unwrap();
    let audit = r.text().await.unwrap();
    assert!(audit.contains("challenge.superseded"), "{audit}");
}

#[tokio::test]
async fn historical_challenge_registered_after_its_successor_is_closed() {
    let app = spawn().await;
    let a_def = pv84();
    let a_id = a_def.id().unwrap();
    // successor first (e.g. ARENA_CHALLENGES_DIR loads files in name order)
    let b = app.register(&pv86(&a_id)).await;
    let a = app.register(&a_def).await;
    assert_eq!(a, a_id);
    let (_, ca) = app.get_json(&format!("/v1/challenges/{a}")).await;
    assert_eq!(
        (ca["open"].clone(), ca["superseded_by"].clone()),
        (json!(false), json!(b))
    );
    let (s, _) = submit_status(&app, &a, b"late", "late").await;
    assert_eq!(s, 409);
    // re-registering the same definition is a no-op and does not reopen anything
    let a2 = app.register(&a_def).await;
    assert_eq!(a2, a);
    let (_, ca) = app.get_json(&format!("/v1/challenges/{a}")).await;
    assert_eq!(ca["open"], json!(false));
}
