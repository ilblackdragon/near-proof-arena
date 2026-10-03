//! End-to-end pipeline tests against the shared Postgres. Each test creates and
//! drops its own `arena_server_test_*` database. All pipeline results here come
//! from the FAKE worker and are therefore tier DEMO.

mod common;

use arena_jobs::*;
use arena_orchestrator::report::{self, SignedReport};
use arena_types::challenge::Tier;
use arena_types::*;
use common::fake_worker::kinds_set;
use common::*;
use serde_json::{json, Value};
use std::time::Duration;

#[tokio::test]
async fn submit_jobs_decision_leaderboard_report_and_events() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-a")).await;
    let v = app.submit(&chal, b"package-1", "k1", None).await;
    assert_eq!(v.stage, Stage::Received);
    assert_eq!(v.decision, None);
    assert_eq!(v.accepted, None);
    assert_eq!(v.tier, Tier::Demo);

    let w = app.fake_worker();
    let kinds = w.drain().await;
    assert_eq!(
        kinds_set(&kinds),
        kinds_set(&JobKind::ALL),
        "every stage ran exactly once: {kinds:?}"
    );
    assert_eq!(kinds.len(), 6);
    assert_eq!(kinds[0], JobKind::Validate);
    assert_eq!(*kinds.last().unwrap(), JobKind::Benchmark);

    let v = app.view(&v.id).await;
    assert_eq!(v.stage, Stage::Decided);
    assert_eq!(v.decision, Some(Decision::Admitted));
    assert_eq!(v.accepted, Some(true));
    assert_eq!(v.tier, Tier::Demo, "fake-worker results are DEMO tier");
    assert!(v.reason_codes.contains(&ReasonCode::DemoOnly));
    assert_eq!(v.candidate_name, "fake-prover");
    assert_eq!(v.change_class, Some(ChangeClass::NoParent));
    // score recomputed by the server: 2x faster than baseline on every class => 200.000
    assert_eq!(v.score_milli, Some(200_000));
    assert_eq!(v.benchmark.as_ref().unwrap().score_milli, Some(200_000));
    assert_eq!(v.gates.len(), all_obligations().len());
    for g in &v.gates {
        assert!(g.reason_codes.contains(&ReasonCode::DemoOnly), "{g:?}");
        assert_eq!(
            g.reused_from, None,
            "worker-forged reused_from must be ignored"
        );
        assert!(g.mandatory);
    }
    // additive view fields
    assert!(!v.artifacts.is_empty());
    assert!(v.logs.iter().any(|l| l.text.contains("[DEMO]")));
    assert!(v.verified_surface.is_some());
    assert_eq!(v.build.as_ref().map(|b| b.reproducible), Some(true));
    assert!(v.assumptions.iter().any(|a| a.id == "sha256-cr"));
    assert!(v.trusted_base.iter().any(|t| t.id == "checker-image"));

    // leaderboard: bare array, demo entry present but never ranked
    let (s, lb) = app.get_json(&format!("/v1/leaderboards/{chal}")).await;
    assert_eq!(s, 200);
    let lb: Vec<LeaderboardEntry> = serde_json::from_value(lb).unwrap();
    assert_eq!(lb.len(), 1);
    assert_eq!(lb[0].rank, None);
    assert_eq!(lb[0].tier, Tier::Demo);
    assert_eq!(lb[0].score_ci_milli, Some(500));

    // signed report
    let (s, rep) = app
        .get_json(&format!("/v1/submissions/{}/report", v.id))
        .await;
    assert_eq!(s, 200);
    let rep: SignedReport = serde_json::from_value(rep).unwrap();
    report::verify(&rep).expect("report signature verifies");
    assert_eq!(rep.public_key, app.state.orch.report_public_key_hex());
    assert_eq!(rep.report["run"]["decision"], "ADMITTED");
    assert_eq!(
        rep.report["submission"]["package_digest"],
        json!(v.package_digest)
    );
    assert!(rep.report["disclaimers"].to_string().contains("DEMO"));
    assert_eq!(rep.report["jobs"].as_array().unwrap().len(), 6);
    let mut tampered = rep.clone();
    tampered.report["run"]["score_milli"] = json!(999_999_999);
    assert!(report::verify(&tampered).is_err());

    // SSE: replay all events, stream terminates after the decision
    let text = tokio::time::timeout(
        Duration::from_secs(20),
        app.http
            .get(app.url(&format!("/v1/submissions/{}/events", v.id)))
            .send()
            .await
            .unwrap()
            .text(),
    )
    .await
    .expect("SSE stream ends after decision")
    .unwrap();
    assert!(text.contains("event: stage"));
    assert!(text.contains("event: gate"));
    assert!(text.contains("event: decision"));
    assert!(text.contains("event: done"));
    // resume after the last event id: only "done"
    let last_id: i64 = text
        .lines()
        .filter_map(|l| l.strip_prefix("id: "))
        .map(|s| s.trim().parse().unwrap())
        .max()
        .unwrap();
    let rest = app
        .http
        .get(app.url(&format!("/v1/submissions/{}/events", v.id)))
        .header("Last-Event-ID", last_id.to_string())
        .send()
        .await
        .unwrap()
        .text()
        .await
        .unwrap();
    assert!(
        !rest.contains("event: gate") && rest.contains("event: done"),
        "{rest}"
    );

    // listing endpoints return bare arrays
    let (_, subs) = app
        .get_json(&format!("/v1/submissions?challenge_id={chal}"))
        .await;
    assert_eq!(subs.as_array().unwrap().len(), 1);
    let (_, chals) = app.get_json("/v1/challenges").await;
    assert_eq!(chals.as_array().unwrap().len(), 1);
    let (_, c) = app.get_json(&format!("/v1/challenges/{chal}")).await;
    assert_eq!(c["id"], json!(chal));
    assert!(
        c["registered_at"].is_string() && c["definition"].is_object() && c["digest"].is_string()
    );
}

#[tokio::test]
async fn idempotency_keys() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-idem")).await;
    let v = app.submit(&chal, b"pkg", "same-key", None).await;
    let up: Value = app
        .upload(&app.agent_token, b"pkg")
        .await
        .json()
        .await
        .unwrap();
    // replay: same key + same body -> same submission, 200
    let r = app
        .submit_raw(&app.agent_token, json!({"challenge_id": chal, "upload_digest": up["digest"], "idempotency_key": "same-key"}))
        .await;
    assert_eq!(r.status(), 200);
    let v2: SubmissionView = r.json().await.unwrap();
    assert_eq!(v2.id, v.id);
    // same key, different body -> 409
    let up2: Value = app
        .upload(&app.agent_token, b"pkg-2")
        .await
        .json()
        .await
        .unwrap();
    let r = app
        .submit_raw(&app.agent_token, json!({"challenge_id": chal, "upload_digest": up2["digest"], "idempotency_key": "same-key"}))
        .await;
    assert_eq!(r.status(), 409);
    let e: Value = r.json().await.unwrap();
    assert_eq!(e["error"]["code"], "idempotency_conflict");
    // keys are per agent: bob can use the same key (with his own upload)
    let upb: Value = app
        .upload(&app.agent2_token, b"pkg")
        .await
        .json()
        .await
        .unwrap();
    let r = app
        .submit_raw(&app.agent2_token, json!({"challenge_id": chal, "upload_digest": upb["digest"], "idempotency_key": "same-key"}))
        .await;
    assert_eq!(r.status(), 201);
    // bad key format
    let r = app
        .submit_raw(&app.agent_token, json!({"challenge_id": chal, "upload_digest": up["digest"], "idempotency_key": "bad key!"}))
        .await;
    assert_eq!(r.status(), 400);
    // cannot submit someone else's upload digest
    let r = app
        .submit_raw(
            &app.agent2_token,
            json!({"challenge_id": chal, "upload_digest": up2["digest"], "idempotency_key": "x"}),
        )
        .await;
    assert_eq!(r.status(), 400);
    let (n,): (i64,) = arena_db::sqlx::query_as("SELECT count(*) FROM submissions")
        .fetch_one(&app.pool)
        .await
        .unwrap();
    assert_eq!(n, 2);
    let (runs,): (i64,) = arena_db::sqlx::query_as("SELECT count(*) FROM runs")
        .fetch_one(&app.pool)
        .await
        .unwrap();
    assert_eq!(runs, 2, "replays do not start runs");
}

#[tokio::test]
async fn cancellation() {
    let app = spawn().await;
    let chal = app
        .register(&challenge_def(Tier::Demo, "demo-cancel"))
        .await;
    let v = app.submit(&chal, b"pkg", "c1", None).await;
    let w = app.fake_worker();
    let job = w.lease(&[], None).await.expect("validate job");
    assert_eq!(job.kind, JobKind::Validate);

    // only the owner can cancel
    let r = app
        .http
        .post(app.url(&format!("/v1/submissions/{}/cancel", v.id)))
        .bearer_auth(&app.agent2_token)
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 403);
    let r = app
        .http
        .post(app.url(&format!("/v1/submissions/{}/cancel", v.id)))
        .bearer_auth(&app.agent_token)
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 200);
    let cv: SubmissionView = r.json().await.unwrap();
    assert_eq!(cv.decision, Some(Decision::Cancelled));
    assert_eq!(cv.accepted, Some(false));
    assert!(cv.reason_codes.contains(&ReasonCode::Cancelled));

    // the worker learns about it on heartbeat and cannot complete
    let hb = w
        .client
        .heartbeat(
            &job.job_id,
            &HeartbeatRequest {
                lease_id: job.lease_id.clone(),
                extend_seconds: None,
            },
        )
        .await
        .unwrap();
    assert!(hb.cancelled);
    let result = w.result_for(&job).await;
    let err = w
        .client
        .complete(
            &job.job_id,
            &CompleteRequest {
                lease_id: job.lease_id.clone(),
                result,
            },
        )
        .await
        .unwrap_err();
    assert_eq!(err.status(), Some(409));
    assert!(
        w.lease(&[], None).await.is_none(),
        "no work after cancellation"
    );
    assert!(app
        .job_states(&v.id)
        .await
        .iter()
        .all(|(_, s, _)| s == "cancelled"));

    // second cancel conflicts; report exists for the cancelled run
    let r = app
        .http
        .post(app.url(&format!("/v1/submissions/{}/cancel", v.id)))
        .bearer_auth(&app.agent_token)
        .send()
        .await
        .unwrap();
    assert_eq!(r.status(), 409);
    let (s, rep) = app
        .get_json(&format!("/v1/submissions/{}/report", v.id))
        .await;
    assert_eq!(s, 200);
    assert_eq!(rep["report"]["run"]["decision"], "CANCELLED");
    assert!(
        rep["report"]["run"]["not_run_gates"]
            .as_array()
            .unwrap()
            .len()
            >= 13
    );
}

#[tokio::test]
async fn lease_expiry_recovery_and_fencing() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-lease")).await;
    let v = app.submit(&chal, b"pkg", "l1", None).await;
    let crashed = app.fake_worker();
    let stale = crashed.lease(&[], Some(1)).await.unwrap();
    assert_eq!(stale.attempt, 1);
    // nothing else runnable while the lease is live
    assert!(app.fake_worker().lease(&[], None).await.is_none());
    tokio::time::sleep(Duration::from_millis(1600)).await;
    let w2 = app.fake_worker();
    let again = w2
        .lease(&[], None)
        .await
        .expect("expired lease is re-leasable");
    assert_eq!(again.job_id, stale.job_id);
    assert_eq!(again.attempt, 2);
    assert_ne!(again.lease_id, stale.lease_id);
    // the stale worker is fenced out
    let result = crashed.result_for(&stale).await;
    let err = crashed
        .client
        .complete(
            &stale.job_id,
            &CompleteRequest {
                lease_id: stale.lease_id.clone(),
                result,
            },
        )
        .await
        .unwrap_err();
    assert_eq!(err.status(), Some(409));
    let err = crashed
        .client
        .heartbeat(
            &stale.job_id,
            &HeartbeatRequest {
                lease_id: stale.lease_id.clone(),
                extend_seconds: None,
            },
        )
        .await
        .unwrap_err();
    assert_eq!(err.status(), Some(409));
    // the new holder completes and the pipeline finishes
    let result = w2.result_for(&again).await;
    w2.client
        .complete(
            &again.job_id,
            &CompleteRequest {
                lease_id: again.lease_id.clone(),
                result,
            },
        )
        .await
        .unwrap();
    w2.drain().await;
    let v = app.view(&v.id).await;
    assert_eq!(v.decision, Some(Decision::Admitted));
    let (n,): (i64,) = arena_db::sqlx::query_as(
        "SELECT count(*) FROM audit_events WHERE submission_id = $1 AND action = 'job.lease_expired'",
    )
    .bind(&v.id)
    .fetch_one(&app.pool)
    .await
    .unwrap();
    assert_eq!(n, 1);
}

#[tokio::test]
async fn retries_then_infra_error() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-infra")).await;
    let v = app.submit(&chal, b"pkg", "i1", None).await;
    let mut w = app.fake_worker();
    w.behavior.infra_fail = Some(JobKind::Build);
    let kinds = w.drain().await;
    assert_eq!(
        kinds,
        vec![
            JobKind::Validate,
            JobKind::Build,
            JobKind::Build,
            JobKind::Build
        ]
    );
    let v = app.view(&v.id).await;
    assert_eq!(v.decision, Some(Decision::InfraError));
    assert_eq!(v.accepted, Some(false));
    assert!(v.reason_codes.contains(&ReasonCode::InfraError));
    let jobs = app.job_states(&v.id).await;
    assert!(
        jobs.contains(&("BUILD".into(), "failed".into(), 3)),
        "{jobs:?}"
    );
    assert!(v
        .logs
        .iter()
        .any(|l| l.text.contains("simulated infra failure")));
    let (_, rep) = app
        .get_json(&format!("/v1/submissions/{}/report", v.id))
        .await;
    assert_eq!(rep["report"]["run"]["decision"], "INFRA_ERROR");
}

#[tokio::test]
async fn final_lease_expiry_is_reaped_to_infra_error() {
    let app = spawn_with(Opts {
        max_attempts: 2,
        ..Default::default()
    })
    .await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-reap")).await;
    let v = app.submit(&chal, b"pkg", "r1", None).await;
    let w = app.fake_worker();
    for attempt in 1..=2 {
        let j = w.lease(&[], Some(1)).await.expect("lease");
        assert_eq!(j.attempt, attempt);
        tokio::time::sleep(Duration::from_millis(1300)).await;
    }
    assert!(
        w.lease(&[], None).await.is_none(),
        "attempts exhausted: not re-leased"
    );
    assert_eq!(app.state.orch.reap_expired(&app.pool).await.unwrap(), 1);
    let v = app.view(&v.id).await;
    assert_eq!(v.decision, Some(Decision::InfraError));
    assert_eq!(app.state.orch.reap_expired(&app.pool).await.unwrap(), 0);
}

#[tokio::test]
async fn fail_fast_records_not_run_gates() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-ff")).await;
    let v = app.submit(&chal, b"pkg", "f1", None).await;
    let mut w = app.fake_worker();
    w.behavior.fail_gate = Some(ObligationId::BuildReproducible);
    let kinds = w.drain().await;
    assert_eq!(kinds, vec![JobKind::Validate, JobKind::Build]);
    let v = app.view(&v.id).await;
    assert_eq!(v.decision, Some(Decision::Rejected));
    assert_eq!(v.accepted, Some(false));
    assert_eq!(v.score_milli, None);
    let (_, rep) = app
        .get_json(&format!("/v1/submissions/{}/report", v.id))
        .await;
    let not_run: Vec<ObligationId> =
        serde_json::from_value(rep["report"]["run"]["not_run_gates"].clone()).unwrap();
    assert!(not_run.contains(&ObligationId::AxiomAudit));
    assert!(not_run.contains(&ObligationId::Benchmark));
    assert!(!not_run.contains(&ObligationId::BuildReproducible));
}

#[tokio::test]
async fn unknown_mandatory_gate_is_inconclusive() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-unk")).await;
    let v = app.submit(&chal, b"pkg", "u1", None).await;
    let mut w = app.fake_worker();
    w.behavior.unknown_gate = Some(ObligationId::AxiomAudit);
    w.drain().await;
    let v = app.view(&v.id).await;
    assert_eq!(v.decision, Some(Decision::Inconclusive));
    assert_eq!(v.accepted, Some(false));
    assert_eq!(v.score_milli, None);
}

#[tokio::test]
async fn invalid_worker_result_counts_as_failed_attempt() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-bogus")).await;
    let v = app.submit(&chal, b"pkg", "b1", None).await;
    let mut w = app.fake_worker();
    w.behavior.bogus_gate_on = Some(JobKind::Validate);
    let kinds = w.drain().await;
    assert_eq!(kinds, vec![JobKind::Validate; 3]);
    let v = app.view(&v.id).await;
    assert_eq!(v.decision, Some(Decision::InfraError));
    assert!(v
        .logs
        .iter()
        .any(|l| l.text.contains("may not report gate")));
}

#[tokio::test]
async fn sanitizes_candidate_strings() {
    let app = spawn().await;
    let chal = app
        .register(&challenge_def(Tier::Demo, "demo-sanitize"))
        .await;
    let v = app.submit(&chal, b"pkg", "s1", None).await;
    let mut w = app.fake_worker();
    let evil = format!(
        "<script>alert(1)</script>\u{202E}gnp.exe\u{0007}\u{0000}{}",
        "x".repeat(10_000)
    );
    w.behavior.summary = Some(evil);
    w.drain().await;
    let r = app
        .http
        .get(app.url(&format!("/v1/submissions/{}", v.id)))
        .send()
        .await
        .unwrap();
    assert_eq!(r.headers()["content-type"], "application/json");
    assert_eq!(r.headers()["x-content-type-options"], "nosniff");
    let v: SubmissionView = r.json().await.unwrap();
    for g in &v.gates {
        assert!(
            !g.summary.contains('\u{202E}')
                && !g.summary.contains('\u{0007}')
                && !g.summary.contains('\0')
        );
        assert!(g.summary.len() <= 4096, "bounded");
        assert!(
            g.summary.starts_with("<script>"),
            "stored verbatim as plain text, never interpreted"
        );
    }
}

#[tokio::test]
async fn formal_cache_reuse_and_change_classification() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-cache")).await;
    let w = app.fake_worker();
    let a = app.submit(&chal, b"pkg-a", "a", None).await;
    w.drain().await;
    let a = app.view(&a.id).await;
    assert_eq!(a.decision, Some(Decision::Admitted));

    // prover-only change: same verified surface -> formal gates reused, no FORMAL_CHECK job
    let b = app.submit(&chal, b"pkg-b", "b", Some(&a.id)).await;
    let kinds = w.drain().await;
    assert!(!kinds.contains(&JobKind::FormalCheck), "{kinds:?}");
    let b = app.view(&b.id).await;
    assert_eq!(b.change_class, Some(ChangeClass::ProverOnly));
    assert_eq!(b.decision, Some(Decision::Admitted));
    let formal: Vec<&GateResult> = b
        .gates
        .iter()
        .filter(|g| JobKind::FormalCheck.owned_gates().contains(&g.gate))
        .collect();
    assert_eq!(formal.len(), 7);
    assert!(formal
        .iter()
        .all(|g| g.reused_from.as_deref() == Some(a.id.as_str())));
    assert!(b
        .gates
        .iter()
        .filter(|g| g.gate == ObligationId::BuildReproducible)
        .all(|g| g.reused_from.is_none()));

    // invalidate by checker image -> the next prover-only child is re-checked
    let def = challenge_def(Tier::Demo, "demo-cache");
    let (s, inv) = app
        .admin_post(
            "/v1/admin/formal-cache/invalidate",
            json!({"checker_image": def.toolchain_policy.checker_image, "reason": "checker CVE"}),
        )
        .await;
    assert_eq!(s, 200);
    assert_eq!(inv["invalidated"].as_array().unwrap().len(), 1);
    let c = app.submit(&chal, b"pkg-c", "c", Some(&b.id)).await;
    let kinds = w.drain().await;
    assert!(kinds.contains(&JobKind::FormalCheck));
    let c = app.view(&c.id).await;
    assert_eq!(c.change_class, Some(ChangeClass::ProverOnly));
    assert!(c.gates.iter().all(|g| g.reused_from.is_none()));
    // invalidate by assumption id
    let (_, inv) = app
        .admin_post(
            "/v1/admin/formal-cache/invalidate",
            json!({"assumption": "sha256-cr", "reason": "assumption withdrawn"}),
        )
        .await;
    assert_eq!(inv["invalidated"].as_array().unwrap().len(), 1);

    // verifier change -> VERIFIER_OR_PROTOCOL, formal reopened
    let mut w2 = app.fake_worker();
    w2.verifier_tag = "v2".into();
    let e = app.submit(&chal, b"pkg-e", "e", Some(&c.id)).await;
    let kinds = w2.drain().await;
    assert!(kinds.contains(&JobKind::FormalCheck));
    assert_eq!(
        app.view(&e.id).await.change_class,
        Some(ChangeClass::VerifierOrProtocol)
    );
}

#[tokio::test]
async fn admin_rerun_creates_new_run_record() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-rerun")).await;
    let v = app.submit(&chal, b"pkg", "r", None).await;
    let mut w = app.fake_worker();
    w.behavior.fail_gate = Some(ObligationId::AdversarialProofs);
    w.drain().await;
    assert_eq!(app.view(&v.id).await.decision, Some(Decision::Rejected));
    let (s, r) = app
        .admin_post(
            &format!("/v1/admin/submissions/{}/rerun", v.id),
            json!({"reason": "flaky adversarial host"}),
        )
        .await;
    assert_eq!(s, 201, "{r}");
    // pending -> second rerun conflicts
    let (s, _) = app
        .admin_post(
            &format!("/v1/admin/submissions/{}/rerun", v.id),
            json!({"reason": "again"}),
        )
        .await;
    assert_eq!(s, 409);
    // agent-visible view shows the new pending run; the old report is still served
    let pending = app.view(&v.id).await;
    assert_eq!(pending.decision, None);
    let (_, rep) = app
        .get_json(&format!("/v1/submissions/{}/report", v.id))
        .await;
    assert_eq!(rep["report"]["run"]["run_number"], 1);
    app.fake_worker().drain().await;
    let done = app.view(&v.id).await;
    assert_eq!(done.decision, Some(Decision::Admitted));
    let (_, rep) = app
        .get_json(&format!("/v1/submissions/{}/report", v.id))
        .await;
    assert_eq!(rep["report"]["run"]["run_number"], 2);
    assert_eq!(rep["report"]["run"]["trigger"], "rerun");
    let runs: Vec<(i32, Option<String>)> = arena_db::sqlx::query_as(
        "SELECT run_number, decision FROM runs WHERE submission_id = $1 ORDER BY run_number",
    )
    .bind(&v.id)
    .fetch_all(&app.pool)
    .await
    .unwrap();
    assert_eq!(
        runs,
        vec![(1, Some("REJECTED".into())), (2, Some("ADMITTED".into()))]
    );
}

/// Red-team RT-01: the formal cache key (and the change class) must cover the
/// verifier binding. A child that keeps every other digest equal but swaps its
/// NPAI verifier bytecode must NOT inherit the parent's formal PASSes: the
/// certificate was checked against `.interp <old bytecode digest>`.
#[tokio::test]
async fn redteam_formal_cache_covers_npai_bytecode() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-rt01")).await;
    let mut w = app.fake_worker();
    w.behavior.verify_route = Some(VerifyRoute::NpaiV1);
    w.behavior.bytecode_tag = Some("good".into());
    let a = app.submit(&chal, b"pkg-rt01-a", "rt01-a", None).await;
    w.drain().await;
    let a = app.view(&a.id).await;
    assert_eq!(a.decision, Some(Decision::Admitted));
    let vs = a.verified_surface.clone().unwrap();
    assert_eq!(vs.verify_route, Some(VerifyRoute::NpaiV1));
    assert!(vs.verifier_bytecode.is_some());

    // same bytecode: prover-only reuse still works
    let b = app.submit(&chal, b"pkg-rt01-b", "rt01-b", Some(&a.id)).await;
    let kinds = w.drain().await;
    assert!(!kinds.contains(&JobKind::FormalCheck), "{kinds:?}");
    assert_eq!(app.view(&b.id).await.change_class, Some(ChangeClass::ProverOnly));

    // swapped bytecode, every other digest identical: formal must re-run
    w.behavior.bytecode_tag = Some("evil".into());
    let c = app.submit(&chal, b"pkg-rt01-c", "rt01-c", Some(&a.id)).await;
    let kinds = w.drain().await;
    assert!(kinds.contains(&JobKind::FormalCheck), "bytecode swap reused formal gates: {kinds:?}");
    let c = app.view(&c.id).await;
    assert_eq!(c.change_class, Some(ChangeClass::VerifierOrProtocol));
    assert!(c.gates.iter().all(|g| g.reused_from.is_none()));

    // route switch with identical digests: also a verifier change
    w.behavior.verify_route = None;
    w.behavior.bytecode_tag = None;
    let _d = app.submit(&chal, b"pkg-rt01-d", "rt01-d", Some(&a.id)).await;
    let kinds = w.drain().await;
    assert!(kinds.contains(&JobKind::FormalCheck), "{kinds:?}");

    // npai-v1 build without a bytecode digest: fail closed, never admitted
    w.behavior.verify_route = Some(VerifyRoute::NpaiV1);
    let e = app.submit(&chal, b"pkg-rt01-e", "rt01-e", Some(&a.id)).await;
    w.drain().await;
    let e = app.view(&e.id).await;
    assert_ne!(e.decision, Some(Decision::Admitted));
    assert!(e.gates.iter().all(|g| g.reused_from.is_none()));
}

/// Red-team RT-02: revoking a submission must stop its formal results from
/// being reused. Before the fix, re-submitting the very same package (new
/// submission id, not revoked) hit the revoked run's formal-cache entry and
/// inherited its formal PASSes.
#[tokio::test]
async fn redteam_revocation_invalidates_formal_cache() {
    let app = spawn().await;
    let chal = app.register(&challenge_def(Tier::Demo, "demo-rt02")).await;
    let w = app.fake_worker();
    let a = app.submit(&chal, b"pkg-rt02-a", "rt02-a", None).await;
    w.drain().await;
    assert_eq!(app.view(&a.id).await.decision, Some(Decision::Admitted));
    let (s, _) = app
        .admin_post(
            &format!("/v1/admin/submissions/{}/revoke", a.id),
            json!({"reason": "certificate found unsound"}),
        )
        .await;
    assert_eq!(s, 201);
    let b = app.submit(&chal, b"pkg-rt02-b", "rt02-b", Some(&a.id)).await;
    let kinds = w.drain().await;
    assert!(
        kinds.contains(&JobKind::FormalCheck),
        "revoked submission's formal results were reused: {kinds:?}"
    );
    let b = app.view(&b.id).await;
    assert!(b.gates.iter().all(|g| g.reused_from.is_none()));
}
