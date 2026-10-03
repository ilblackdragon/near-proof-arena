//! Stable process exit codes for `arena`. These are part of the agent-facing
//! contract (`docs/AGENT_CONTRACT.md` §9) — never renumber, only append.

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Exit {
    /// Command succeeded (for `status --watch` / `submit --watch`: decision ADMITTED).
    Ok = 0,
    /// Unexpected internal error (bug, I/O error on local files).
    Internal = 1,
    /// Bad command-line usage (emitted by the argument parser).
    Usage = 2,
    /// Local package / manifest / archive validation or local check failed.
    LocalCheckFailed = 3,
    /// Missing or rejected credentials (no token, HTTP 401/403), bad config file.
    Auth = 4,
    /// Server unreachable, timed out, HTTP 5xx or 429. Safe to retry with the
    /// same idempotency key.
    Unavailable = 5,
    /// Server rejected the request (HTTP 400/409/413/422 and other 4xx).
    Rejected = 6,
    /// Resource not found (HTTP 404).
    NotFound = 7,
    /// Watched submission decided REJECTED.
    DecisionRejected = 10,
    /// Watched submission decided INCONCLUSIVE.
    DecisionInconclusive = 11,
    /// Watched submission decided INFRA_ERROR.
    DecisionInfraError = 12,
    /// Watched submission decided CANCELLED.
    DecisionCancelled = 13,
}

impl Exit {
    pub fn code(self) -> u8 {
        self as u8
    }
}

/// Error carrying the exit code it maps to.
#[derive(Debug)]
pub struct CliError {
    pub exit: Exit,
    pub msg: String,
}

impl CliError {
    pub fn new(exit: Exit, msg: impl Into<String>) -> Self {
        CliError {
            exit,
            msg: msg.into(),
        }
    }
    pub fn internal(msg: impl Into<String>) -> Self {
        Self::new(Exit::Internal, msg)
    }
    pub fn local(msg: impl Into<String>) -> Self {
        Self::new(Exit::LocalCheckFailed, msg)
    }
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.msg)
    }
}

impl From<std::io::Error> for CliError {
    fn from(e: std::io::Error) -> Self {
        CliError::internal(format!("i/o error: {e}"))
    }
}

pub type CliResult<T> = Result<T, CliError>;

/// Map a decided submission to its exit code.
pub fn exit_for_decision(d: arena_types::Decision) -> Exit {
    use arena_types::Decision::*;
    match d {
        Admitted => Exit::Ok,
        Rejected => Exit::DecisionRejected,
        Inconclusive => Exit::DecisionInconclusive,
        InfraError => Exit::DecisionInfraError,
        Cancelled => Exit::DecisionCancelled,
    }
}
