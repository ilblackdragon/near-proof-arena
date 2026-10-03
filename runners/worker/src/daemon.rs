//! Worker loop: lease → execute (with heartbeats) → complete / fail.

use crate::client::{ClientError, CompleteRequest, ControlPlane, FailRequest, HeartbeatRequest, LeaseRequest};
use crate::executor::{ExecError, JobExecutor};
use crate::jobs::{JobKind, SandboxInfo};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

pub struct Daemon {
    pub control: Arc<dyn ControlPlane>,
    pub executor: Arc<dyn JobExecutor>,
    pub worker_id: String,
    pub kinds: Vec<JobKind>,
    pub sandbox: SandboxInfo,
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

impl Daemon {
    /// Lease and process at most one job.
    pub fn run_once(&self) -> Result<Step, ClientError> {
        let lease = LeaseRequest { worker_id: self.worker_id.clone(), kinds: self.kinds.clone(), sandbox: self.sandbox.clone() };
        let Some(job) = self.control.lease(&lease)? else { return Ok(Step::Idle) };
        log(&format!("leased job {} ({}, attempt {})", job.id, job.spec.kind().as_str(), job.attempt));
        if !self.kinds.contains(&job.spec.kind()) {
            self.control.fail(&FailRequest {
                job_id: job.id.clone(),
                worker_id: self.worker_id.clone(),
                attempt: job.attempt,
                error: format!("worker does not run {} jobs", job.spec.kind().as_str()),
                retryable: true,
            })?;
            return Ok(Step::Failed);
        }

        let cancel = Arc::new(AtomicBool::new(false));
        let done = Arc::new((Mutex::new(false), Condvar::new()));
        let hb = {
            let control = self.control.clone();
            let req = HeartbeatRequest { job_id: job.id.clone(), worker_id: self.worker_id.clone(), attempt: job.attempt };
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
                    match control.heartbeat(&req) {
                        Ok(_) => {}
                        Err(ClientError::LeaseLost) => {
                            log(&format!("lease lost for job {}", req.job_id));
                            cancel.store(true, Ordering::SeqCst);
                            return;
                        }
                        Err(e) => log(&format!("heartbeat error (will retry): {e}")),
                    }
                }
            })
        };
        let result = self.executor.execute(&job, &cancel);
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
            Ok(output) => {
                let req = CompleteRequest { job_id: job.id.clone(), worker_id: self.worker_id.clone(), attempt: job.attempt, output };
                match self.control.complete(&req) {
                    Ok(()) => {
                        log(&format!("completed job {}", job.id));
                        Ok(Step::Completed)
                    }
                    Err(ClientError::LeaseLost) => Ok(Step::LeaseLost),
                    Err(e) => Err(e),
                }
            }
            Err(ExecError::Cancelled) => Ok(Step::LeaseLost),
            Err(ExecError::Violation(e)) => {
                // Normally converted into a FAIL gate by the executor.
                self.control.fail(&FailRequest { job_id: job.id.clone(), worker_id: self.worker_id.clone(), attempt: job.attempt, error: format!("sandbox violation: {e}"), retryable: false })?;
                Ok(Step::Failed)
            }
            Err(ExecError::Infra(e)) => {
                log(&format!("job {} infra failure: {e}", job.id));
                let mut msg = e;
                msg.truncate(2000);
                self.control.fail(&FailRequest { job_id: job.id.clone(), worker_id: self.worker_id.clone(), attempt: job.attempt, error: msg, retryable: true })?;
                Ok(Step::Failed)
            }
        }
    }

    pub fn run_forever(&self, stop: &AtomicBool) {
        while !stop.load(Ordering::SeqCst) {
            match self.run_once() {
                Ok(Step::Idle) => std::thread::sleep(self.poll_interval),
                Ok(_) => {}
                Err(ClientError::Unauthorized) => {
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
