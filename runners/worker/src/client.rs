//! Worker ↔ control-plane protocol (internal worker API).
//!
//! The worker authenticates with a worker bearer token only; it never holds
//! database credentials. Endpoints (all JSON unless noted):
//!
//! ```text
//! POST /internal/v1/jobs/lease      {worker_id, kinds[], sandbox}       -> 200 Job | 204
//! POST /internal/v1/jobs/heartbeat  {job_id, worker_id, attempt}        -> 200 {lease_until} | 409 lease lost
//! POST /internal/v1/jobs/complete   {job_id, worker_id, attempt, output: JobOutput} -> 200
//! POST /internal/v1/jobs/fail       {job_id, worker_id, attempt, error, retryable} -> 200
//! GET  /internal/v1/artifacts/{digest}   -> raw bytes
//! PUT  /internal/v1/artifacts/{digest}   raw bytes -> 200/201
//! ```

use crate::jobs::{Job, JobKind, JobOutput, SandboxInfo};
use crate::store::{ArtifactStore, StoreError};
use arena_types::Digest;
use serde::{Deserialize, Serialize};
use std::io::Read;
use std::time::Duration;

#[derive(Debug, thiserror::Error)]
pub enum ClientError {
    #[error("lease lost")]
    LeaseLost,
    #[error("unauthorized (check worker token)")]
    Unauthorized,
    #[error("http {0}: {1}")]
    Status(u16, String),
    #[error("transport: {0}")]
    Transport(String),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LeaseRequest {
    pub worker_id: String,
    pub kinds: Vec<JobKind>,
    pub sandbox: SandboxInfo,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HeartbeatRequest {
    pub job_id: String,
    pub worker_id: String,
    pub attempt: u32,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HeartbeatResponse {
    pub lease_until: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CompleteRequest {
    pub job_id: String,
    pub worker_id: String,
    pub attempt: u32,
    pub output: JobOutput,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FailRequest {
    pub job_id: String,
    pub worker_id: String,
    pub attempt: u32,
    /// Sanitized, bounded, never contains held-out data.
    pub error: String,
    /// Infra failures are retryable (bounded by the server: 3 attempts).
    pub retryable: bool,
}

pub trait ControlPlane: Send + Sync {
    fn lease(&self, req: &LeaseRequest) -> Result<Option<Job>, ClientError>;
    fn heartbeat(&self, req: &HeartbeatRequest) -> Result<HeartbeatResponse, ClientError>;
    fn complete(&self, req: &CompleteRequest) -> Result<(), ClientError>;
    fn fail(&self, req: &FailRequest) -> Result<(), ClientError>;
}

pub struct HttpControlPlane {
    base: String,
    token: String,
    agent: ureq::Agent,
}

impl HttpControlPlane {
    pub fn new(base_url: &str, token: &str) -> Self {
        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_secs(10))
            .timeout(Duration::from_secs(600))
            .redirects(0)
            .build();
        HttpControlPlane { base: base_url.trim_end_matches('/').to_string(), token: token.to_string(), agent }
    }

    fn url(&self, path: &str) -> String {
        format!("{}{}", self.base, path)
    }

    fn auth(&self, r: ureq::Request) -> ureq::Request {
        r.set("Authorization", &format!("Bearer {}", self.token))
    }

    fn post<T: Serialize>(&self, path: &str, body: &T) -> Result<ureq::Response, ClientError> {
        let r = self.auth(self.agent.post(&self.url(path)));
        map(r.send_json(serde_json::to_value(body).map_err(|e| ClientError::Transport(e.to_string()))?))
    }
}

fn map(r: Result<ureq::Response, ureq::Error>) -> Result<ureq::Response, ClientError> {
    match r {
        Ok(resp) => Ok(resp),
        Err(ureq::Error::Status(401 | 403, _)) => Err(ClientError::Unauthorized),
        Err(ureq::Error::Status(409, _)) => Err(ClientError::LeaseLost),
        Err(ureq::Error::Status(code, resp)) => {
            let mut s = String::new();
            let _ = resp.into_reader().take(2048).read_to_string(&mut s);
            Err(ClientError::Status(code, s))
        }
        Err(e) => Err(ClientError::Transport(e.to_string())),
    }
}

fn json<T: serde::de::DeserializeOwned>(resp: ureq::Response) -> Result<T, ClientError> {
    let mut buf = Vec::new();
    resp.into_reader().take(64 << 20).read_to_end(&mut buf).map_err(|e| ClientError::Transport(e.to_string()))?;
    serde_json::from_slice(&buf).map_err(|e| ClientError::Transport(format!("bad JSON from server: {e}")))
}

impl ControlPlane for HttpControlPlane {
    fn lease(&self, req: &LeaseRequest) -> Result<Option<Job>, ClientError> {
        let resp = self.post("/internal/v1/jobs/lease", req)?;
        if resp.status() == 204 {
            return Ok(None);
        }
        json(resp).map(Some)
    }
    fn heartbeat(&self, req: &HeartbeatRequest) -> Result<HeartbeatResponse, ClientError> {
        json(self.post("/internal/v1/jobs/heartbeat", req)?)
    }
    fn complete(&self, req: &CompleteRequest) -> Result<(), ClientError> {
        self.post("/internal/v1/jobs/complete", req).map(|_| ())
    }
    fn fail(&self, req: &FailRequest) -> Result<(), ClientError> {
        self.post("/internal/v1/jobs/fail", req).map(|_| ())
    }
}

impl ArtifactStore for HttpControlPlane {
    fn get_raw(&self, digest: &Digest, max_bytes: u64) -> Result<Vec<u8>, StoreError> {
        let r = self.auth(self.agent.get(&self.url(&format!("/internal/v1/artifacts/{digest}"))));
        let resp = match r.call() {
            Ok(r) => r,
            Err(ureq::Error::Status(404, _)) => return Err(StoreError::NotFound(digest.clone())),
            Err(e) => return Err(StoreError::Transport(e.to_string())),
        };
        let mut buf = Vec::new();
        resp.into_reader().take(max_bytes.saturating_add(1)).read_to_end(&mut buf)?;
        if buf.len() as u64 > max_bytes {
            return Err(StoreError::TooLarge(digest.clone(), max_bytes));
        }
        Ok(buf)
    }
    fn put(&self, bytes: &[u8]) -> Result<Digest, StoreError> {
        let d = Digest::of_bytes(bytes);
        let r = self
            .auth(self.agent.put(&self.url(&format!("/internal/v1/artifacts/{d}"))))
            .set("Content-Type", "application/octet-stream");
        r.send_bytes(bytes).map_err(|e| StoreError::Transport(e.to_string()))?;
        Ok(d)
    }
}
