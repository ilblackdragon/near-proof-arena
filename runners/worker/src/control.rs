//! Worker ↔ control plane, over `server/arena-jobs`' typed `WorkerClient`
//! (`/internal/v1/jobs/lease`, `/jobs/{id}/heartbeat|complete|fail`,
//! `GET|PUT /internal/v1/artifacts/{digest}`; worker bearer token only).
//!
//! The worker's execution code is synchronous; [`HttpControl`] owns a small
//! tokio runtime and blocks on the async client.

use crate::store::{ArtifactStore, StoreError};
use arena_jobs::client::{ClientError, WorkerClient};
use arena_jobs::{
    CompleteRequest, FailRequest, HeartbeatRequest, HeartbeatResponse, LeaseRequest, LeasedJob,
};
use arena_types::Digest;

#[derive(Debug, thiserror::Error)]
pub enum ControlError {
    #[error("unauthorized (check the worker token)")]
    Unauthorized,
    /// The lease is no longer ours (expired, re-leased, run cancelled).
    #[error("lease lost: {0}")]
    LeaseLost(String),
    #[error("control plane: {0}")]
    Other(String),
}

impl From<ClientError> for ControlError {
    fn from(e: ClientError) -> Self {
        match e.status() {
            Some(401 | 403) => ControlError::Unauthorized,
            Some(409 | 410) => ControlError::LeaseLost(e.to_string()),
            _ => ControlError::Other(e.to_string()),
        }
    }
}

/// Synchronous seam over the worker API (tests substitute fakes).
pub trait ControlPlane: Send + Sync {
    fn lease(&self, req: &LeaseRequest) -> Result<Option<LeasedJob>, ControlError>;
    fn heartbeat(
        &self,
        job_id: &str,
        req: &HeartbeatRequest,
    ) -> Result<HeartbeatResponse, ControlError>;
    fn complete(&self, job_id: &str, req: &CompleteRequest) -> Result<(), ControlError>;
    fn fail(&self, job_id: &str, req: &FailRequest) -> Result<(), ControlError>;
}

pub struct HttpControl {
    rt: tokio::runtime::Runtime,
    client: WorkerClient,
}

impl HttpControl {
    pub fn new(base_url: &str, token: &str) -> Result<Self, ControlError> {
        let rt = tokio::runtime::Builder::new_multi_thread()
            .worker_threads(2)
            .enable_all()
            .build()
            .map_err(|e| ControlError::Other(e.to_string()))?;
        let client = WorkerClient::new(base_url, token).map_err(ControlError::from)?;
        Ok(HttpControl { rt, client })
    }
}

impl ControlPlane for HttpControl {
    fn lease(&self, req: &LeaseRequest) -> Result<Option<LeasedJob>, ControlError> {
        Ok(self.rt.block_on(self.client.lease(req))?)
    }
    fn heartbeat(
        &self,
        job_id: &str,
        req: &HeartbeatRequest,
    ) -> Result<HeartbeatResponse, ControlError> {
        Ok(self.rt.block_on(self.client.heartbeat(job_id, req))?)
    }
    fn complete(&self, job_id: &str, req: &CompleteRequest) -> Result<(), ControlError> {
        self.rt.block_on(self.client.complete(job_id, req))?;
        Ok(())
    }
    fn fail(&self, job_id: &str, req: &FailRequest) -> Result<(), ControlError> {
        self.rt.block_on(self.client.fail(job_id, req))?;
        Ok(())
    }
}

impl ArtifactStore for HttpControl {
    fn get_raw(&self, digest: &Digest, max_bytes: u64) -> Result<Vec<u8>, StoreError> {
        match self.rt.block_on(self.client.get_artifact(digest)) {
            Ok(Some(b)) if b.len() as u64 > max_bytes => {
                Err(StoreError::TooLarge(digest.clone(), max_bytes))
            }
            Ok(Some(b)) => Ok(b.to_vec()),
            Ok(None) => Err(StoreError::NotFound(digest.clone())),
            Err(e) => Err(StoreError::Transport(e.to_string())),
        }
    }
    fn put(&self, bytes: &[u8]) -> Result<Digest, StoreError> {
        let d = Digest::of_bytes(bytes);
        self.rt
            .block_on(self.client.put_artifact(&d, bytes.to_vec()))
            .map_err(|e| StoreError::Transport(e.to_string()))?;
        Ok(d)
    }
}
