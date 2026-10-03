//! Worker loop: lease → execute (with heartbeats) → complete / fail.

use crate::control::{ControlError, ControlPlane};
use crate::executor::{ExecError, JobExecutor};
use arena_jobs::{
    CompleteRequest, FailRequest, HeartbeatRequest, JobKind, LeaseRequest, JOB_PROTOCOL_VERSION,
};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

pub struct Daemon {
    pub control: Arc<dyn ControlPlane>,
    pub executor: Arc<dyn JobExecutor>,
    pub kinds: Vec<JobKind>,
    pub lease_seconds: u32,
    pub poll_interval: Duration,
    pub heartbeat_interval: Duration,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Step {
    Idle,
    Completed,
    Failed,
    LeaseLost,
}

fn log(msg: &str) {
    eprintln!("[arena-worker] {msg}");
}

fn bounded(mut s: String) -> String {
    if s.len() > 2000 {
        let mut i = 2000;
        while !s.is_char_boundary(i) {
            i -= 1;
        }
        s.truncate(i);
    }
    s
}

impl Daemon {
    /// Lease and process at most one job.
    pub fn run_once(&self) -> Result<Step, ControlError> {
        let lease = LeaseRequest {
            kinds: self.kinds.clone(),
            lease_seconds: Some(self.lease_seconds),
        };
        let Some(job) = self.control.lease(&lease)? else {
            return Ok(Step::Idle);
        };
        log(&format!(
            "leased job {} ({}, attempt {}/{})",
            job.job_id, job.kind, job.attempt, job.max_attempts
        ));
        let fail = |error: String, retryable: bool| -> Result<Step, ControlError> {
            log(&format!(
                "job {} failed (retryable={retryable}): {error}",
                job.job_id
            ));
            match self.control.fail(
                &job.job_id,
                &FailRequest {
                    lease_id: job.lease_id.clone(),
                    error: bounded(error),
                    retryable,
                },
            ) {
                Ok(()) => Ok(Step::Failed),
                Err(ControlError::LeaseLost(_)) => Ok(Step::LeaseLost),
                Err(e) => Err(e),
            }
        };
        if job.protocol != JOB_PROTOCOL_VERSION {
            return fail(
                format!("unsupported job protocol {:?}", job.protocol),
                false,
            );
        }
        if !self.kinds.contains(&job.kind) || job.spec.kind() != job.kind {
            return fail(format!("worker does not run {} jobs", job.kind), true);
        }

        let cancel = Arc::new(AtomicBool::new(false));
        let done = Arc::new((Mutex::new(false), Condvar::new()));
        let hb = {
            let control = self.control.clone();
            let job_id = job.job_id.clone();
            let req = HeartbeatRequest {
                lease_id: job.lease_id.clone(),
                extend_seconds: Some(self.lease_seconds),
            };
            let cancel = cancel.clone();
            let done = done.clone();
            let every = self.heartbeat_interval;
            std::thread::spawn(move || {
                let (m, cv) = &*done;
                let mut g = m.lock().unwrap();
                loop {
                    g = cv.wait_timeout(g, every).unwrap().0;
                    if *g {
                        return;
                    }
                    match control.heartbeat(&job_id, &req) {
                        Ok(r) if r.cancelled => {
                            log(&format!("job {job_id} cancelled by the control plane"));
                            cancel.store(true, Ordering::SeqCst);
                            return;
                        }
                        Ok(_) => {}
                        Err(ControlError::LeaseLost(e)) => {
                            log(&format!("lease lost for job {job_id}: {e}"));
                            cancel.store(true, Ordering::SeqCst);
                            return;
                        }
                        Err(e) => log(&format!("heartbeat error (will retry): {e}")),
                    }
                }
            })
        };
        let key = format!("{}-{}", job.job_id, job.attempt);
        let result = self.executor.execute(&job.spec, &key, &cancel);
        {
            let (m, cv) = &*done;
            *m.lock().unwrap() = true;
            cv.notify_all();
        }
        let _ = hb.join();
        if cancel.load(Ordering::SeqCst) {
            return Ok(Step::LeaseLost);
        }
        match result {
            Ok(result) => match self.control.complete(
                &job.job_id,
                &CompleteRequest {
                    lease_id: job.lease_id.clone(),
                    result,
                },
            ) {
                Ok(()) => {
                    log(&format!("completed job {}", job.job_id));
                    Ok(Step::Completed)
                }
                Err(ControlError::LeaseLost(_)) => Ok(Step::LeaseLost),
                Err(ControlError::Other(e)) => {
                    fail(format!("server rejected the result: {e}"), true)
                }
                Err(e) => Err(e),
            },
            Err(ExecError::Cancelled) => Ok(Step::LeaseLost),
            Err(ExecError::Refused(e)) => fail(e, false),
            Err(ExecError::Violation(e)) => fail(format!("sandbox violation: {e}"), false),
            Err(ExecError::Infra(e)) => fail(e, true),
        }
    }

    pub fn run_forever(&self, stop: &AtomicBool) {
        while !stop.load(Ordering::SeqCst) {
            match self.run_once() {
                Ok(Step::Idle) => std::thread::sleep(self.poll_interval),
                Ok(_) => {}
                Err(ControlError::Unauthorized) => {
                    log("unauthorized: check the worker token; backing off");
                    std::thread::sleep(self.poll_interval * 10);
                }
                Err(e) => {
                    log(&format!("control-plane error: {e}"));
                    std::thread::sleep(self.poll_interval);
                }
            }
        }
    }
}
