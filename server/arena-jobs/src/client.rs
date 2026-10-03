//! Minimal typed client for the worker HTTP API. Enabled with feature `client`.
//!
//! ```no_run
//! # async fn f() -> Result<(), arena_jobs::client::ClientError> {
//! use arena_jobs::{client::WorkerClient, LeaseRequest};
//! let c = WorkerClient::new("http://127.0.0.1:8471", "arena_wrk_...")?;
//! if let Some(job) = c.lease(&LeaseRequest::default()).await? {
//!     // ... run job.spec in a sandbox, then c.complete(...) or c.fail(...)
//! }
//! # Ok(()) }
//! ```

use crate::*;
use bytes::Bytes;

#[derive(Debug, thiserror::Error)]
pub enum ClientError {
    #[error("http: {0}")]
    Http(#[from] reqwest::Error),
    #[error("server returned {status}: {body}")]
    Status { status: u16, body: String },
}

impl ClientError {
    /// HTTP status, if the server answered.
    pub fn status(&self) -> Option<u16> {
        match self {
            ClientError::Status { status, .. } => Some(*status),
            ClientError::Http(e) => e.status().map(|s| s.as_u16()),
        }
    }
}

#[derive(Clone)]
pub struct WorkerClient {
    base: String,
    token: String,
    http: reqwest::Client,
}

impl WorkerClient {
    pub fn new(base_url: &str, token: &str) -> Result<Self, ClientError> {
        let http = reqwest::Client::builder().build()?;
        Ok(Self {
            base: base_url.trim_end_matches('/').to_string(),
            token: token.to_string(),
            http,
        })
    }

    fn url(&self, path: &str) -> String {
        format!("{}{}", self.base, path)
    }

    async fn check(resp: reqwest::Response) -> Result<reqwest::Response, ClientError> {
        if resp.status().is_success() {
            Ok(resp)
        } else {
            let status = resp.status().as_u16();
            let body = resp.text().await.unwrap_or_default();
            Err(ClientError::Status { status, body })
        }
    }

    async fn post<B: Serialize, R: serde::de::DeserializeOwned>(
        &self,
        path: &str,
        body: &B,
    ) -> Result<R, ClientError> {
        let resp = self
            .http
            .post(self.url(path))
            .bearer_auth(&self.token)
            .json(body)
            .send()
            .await?;
        Ok(Self::check(resp).await?.json().await?)
    }

    /// Lease the next runnable job. `Ok(None)` when the queue is empty.
    pub async fn lease(&self, req: &LeaseRequest) -> Result<Option<LeasedJob>, ClientError> {
        let resp = self
            .http
            .post(self.url("/internal/v1/jobs/lease"))
            .bearer_auth(&self.token)
            .json(req)
            .send()
            .await?;
        if resp.status() == reqwest::StatusCode::NO_CONTENT {
            return Ok(None);
        }
        Ok(Some(Self::check(resp).await?.json().await?))
    }

    pub async fn heartbeat(
        &self,
        job_id: &str,
        req: &HeartbeatRequest,
    ) -> Result<HeartbeatResponse, ClientError> {
        self.post(&format!("/internal/v1/jobs/{job_id}/heartbeat"), req)
            .await
    }

    pub async fn complete(
        &self,
        job_id: &str,
        req: &CompleteRequest,
    ) -> Result<AckResponse, ClientError> {
        self.post(&format!("/internal/v1/jobs/{job_id}/complete"), req)
            .await
    }

    pub async fn fail(&self, job_id: &str, req: &FailRequest) -> Result<AckResponse, ClientError> {
        self.post(&format!("/internal/v1/jobs/{job_id}/fail"), req)
            .await
    }

    /// Fetch an artifact by digest. The caller should re-hash the bytes.
    pub async fn get_artifact(&self, digest: &Digest) -> Result<Option<Bytes>, ClientError> {
        let resp = self
            .http
            .get(self.url(&format!("/internal/v1/artifacts/{digest}")))
            .bearer_auth(&self.token)
            .send()
            .await?;
        if resp.status() == reqwest::StatusCode::NOT_FOUND {
            return Ok(None);
        }
        Ok(Some(Self::check(resp).await?.bytes().await?))
    }

    /// Upload an artifact; the server verifies that the body hashes to `digest`.
    pub async fn put_artifact(
        &self,
        digest: &Digest,
        bytes: impl Into<reqwest::Body>,
    ) -> Result<ArtifactPutResponse, ClientError> {
        let resp = self
            .http
            .put(self.url(&format!("/internal/v1/artifacts/{digest}")))
            .bearer_auth(&self.token)
            .body(bytes)
            .send()
            .await?;
        Ok(Self::check(resp).await?.json().await?)
    }
}
