//! Daemon loop against an in-process control plane: lease → execute →
//! complete / fail, heartbeats, cancellation, tier refusal.

mod common;

use arena_jobs::*;
use arena_types::{GateStatus, ObligationId};
use arena_worker::control::{ControlError, ControlPlane};
use arena_worker::daemon::{Daemon, Step};
use common::*;
use std::sync::{Arc, Mutex};
use std::time::Duration;

#[derive(Default)]
struct Fake {
    jobs: Mutex<Vec<LeasedJob>>,
    completed: Mutex<Vec<(String, CompleteRequest)>>,
    failed: Mutex<Vec<(String, FailRequest)>>,
    heartbeats: Mutex<usize>,
    cancel: bool,
}

impl ControlPlane for Fake {
    fn lease(&self, req: &LeaseRequest) -> Result<Option<LeasedJob>, ControlError> {
        assert!(!req.kinds.is_empty());
        Ok(self.jobs.lock().unwrap().pop())
    }
    fn heartbeat(&self, _: &str, req: &HeartbeatRequest) -> Result<HeartbeatResponse, ControlError> {
        assert_eq!(req.lease_id, "lease-1");
        *self.heartbeats.lock().unwrap() += 1;
        Ok(HeartbeatResponse { lease_until: "2099-01-01T00:00:00Z".into(), cancelled: self.cancel })
    }
    fn complete(&self, id: &str, req: &CompleteRequest) -> Result<(), ControlError> {
        self.completed.lock().unwrap().push((id.into(), req.clone()));
        Ok(())
    }
    fn fail(&self, id: &str, req: &FailRequest) -> Result<(), ControlError> {
        self.failed.lock().unwrap().push((id.into(), req.clone()));
        Ok(())
    }
}

fn leased(spec: JobSpec) -> LeasedJob {
    LeasedJob {
        job_id: "job-1".into(),
        lease_id: "lease-1".into(),
        submission_id: "sub_test".into(),
        run_id: "run_test".into(),
        kind: spec.kind(),
        attempt: 1,
        max_attempts: 3,
        lease_until: "2099-01-01T00:00:00Z".into(),
        protocol: JOB_PROTOCOL_VERSION.into(),
        spec,
    }
}

fn daemon(f: &Fixture, control: Arc<Fake>) -> Daemon {
    let exec = common::executor(f.exec.ctx.sandbox.clone(), f.store.clone(), &f.tmp.path().join("djobs"));
    Daemon {
        control,
        kinds: exec.kinds(),
        executor: Arc::new(exec),
        lease_seconds: 60,
        poll_interval: Duration::from_millis(10),
        heartbeat_interval: Duration::from_millis(20),
    }
}

#[test]
fn lease_execute_complete_and_refusals() {
    let f = fixture();
    let fake = Arc::new(Fake::default());
    let d = daemon(&f, fake.clone());
    assert_eq!(d.run_once().unwrap(), Step::Idle);
    assert!(!d.kinds.contains(&JobKind::FormalCheck), "formal check needs a formal config");

    let pkg = f.put(&tar_of(&package_files()));
    fake.jobs.lock().unwrap().push(leased(JobSpec::Validate(ValidateJob { ctx: f.ctx(&pkg), challenge: f.chal.clone() })));
    assert_eq!(d.run_once().unwrap(), Step::Completed);
    let (id, done) = fake.completed.lock().unwrap().pop().unwrap();
    assert_eq!(id, "job-1");
    assert_eq!(done.lease_id, "lease-1");
    assert_eq!(done.result.gates[0].status, GateStatus::Pass);
    assert_eq!(done.result.gates[0].gate, ObligationId::PkgWellformed);
    for a in &done.result.artifacts {
        assert!(f.store.root.join(a.digest.hex()).exists(), "artifacts are uploaded before completion");
    }

    // A formal-tier job is refused (non-retryable) by a demo-capped sandbox.
    let mut ctx = f.ctx(&pkg);
    ctx.tier = arena_types::challenge::Tier::Formal;
    fake.jobs.lock().unwrap().push(leased(JobSpec::Validate(ValidateJob { ctx, challenge: f.chal.clone() })));
    assert_eq!(d.run_once().unwrap(), Step::Failed);
    let (_, fr) = fake.failed.lock().unwrap().pop().unwrap();
    assert!(!fr.retryable && fr.error.contains("tier"), "{fr:?}");

    // Missing input: retryable infra failure.
    fake.jobs.lock().unwrap().push(leased(JobSpec::Validate(ValidateJob { ctx: f.ctx(&arena_types::Digest::of_bytes(b"nope")), challenge: f.chal.clone() })));
    assert_eq!(d.run_once().unwrap(), Step::Failed);
    let (_, fr) = fake.failed.lock().unwrap().pop().unwrap();
    assert!(fr.retryable && fr.error.contains("not found"), "{fr:?}");

    // Unknown protocol version: refused.
    let mut j = leased(JobSpec::Validate(ValidateJob { ctx: f.ctx(&pkg), challenge: f.chal.clone() }));
    j.protocol = "arena-jobs-v999".into();
    fake.jobs.lock().unwrap().push(j);
    assert_eq!(d.run_once().unwrap(), Step::Failed);
    assert!(!fake.failed.lock().unwrap().pop().unwrap().1.retryable);
}

#[test]
fn cancellation_via_heartbeat() {
    let f = fixture();
    let fake = Arc::new(Fake { cancel: true, ..Default::default() });
    let d = daemon(&f, fake.clone());
    let (v, pkg) = f.validate(&package_files());
    let manifest = v.manifest.unwrap();
    fake.jobs.lock().unwrap().push(leased(JobSpec::Build(BuildJob { ctx: f.ctx(&pkg), challenge: f.chal.clone(), manifest })));
    assert_eq!(d.run_once().unwrap(), Step::LeaseLost);
    assert!(fake.completed.lock().unwrap().is_empty(), "a cancelled job is never completed");
    assert!(*fake.heartbeats.lock().unwrap() >= 1);
}

#[test]
fn binary_refuses_db_credentials() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_arena-worker"))
        .arg("once")
        .env_clear()
        .env("ARENA_SERVER_URL", "http://127.0.0.1:1")
        .env("ARENA_WORKER_TOKEN", "t")
        .env("DATABASE_URL", "postgres://arena:arena@127.0.0.1:55471/arena")
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("database credentials"));
}
