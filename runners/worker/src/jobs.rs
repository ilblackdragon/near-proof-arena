//! Job types: the single source is `server/arena-jobs` (re-exported here).
//! Only worker-internal helpers are defined locally.

pub use arena_jobs::{
    BuildJob, BuildOutputs, ExecJob, ExecutionInfo, FormalCheckJob, JobContext, JobKind, JobResult,
    JobSpec, LeasedJob, ValidateJob,
};
use arena_types::{ChallengeDefinition, Digest};

/// Limits for running entry points, from the challenge's `resource_limits`
/// and `claim_encoding` (+ worker-side caps on pids / scratch).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunLimits {
    pub max_prepare_ms: u64,
    pub max_prove_ms: u64,
    pub max_verify_ms: u64,
    pub max_ram_bytes: u64,
    pub max_proof_bytes: u64,
    pub max_claim_bytes: u64,
    pub max_request_bytes: u64,
    pub max_witness_bytes: u64,
    pub max_public_artifact_bytes: u64,
    pub max_pids: u32,
    pub scratch_mb: u64,
}

impl RunLimits {
    pub fn from_challenge(c: &ChallengeDefinition) -> Self {
        let r = &c.resource_limits;
        let per_run = if c.measurement.per_run_timeout_ms > 0 {
            c.measurement.per_run_timeout_ms
        } else {
            u64::MAX
        };
        RunLimits {
            max_prepare_ms: r.max_prepare_ms,
            max_prove_ms: r.max_prove_ms.min(per_run),
            max_verify_ms: r.max_verify_ms,
            max_ram_bytes: r.max_ram_bytes,
            max_proof_bytes: r.max_proof_bytes,
            max_claim_bytes: c.claim_encoding.max_claim_bytes,
            max_request_bytes: c.claim_encoding.max_request_bytes,
            max_witness_bytes: c.claim_encoding.max_witness_bytes,
            max_public_artifact_bytes: r.max_public_artifact_bytes,
            max_pids: 256,
            scratch_mb: ((r.max_proof_bytes
                + c.claim_encoding.max_claim_bytes
                + r.max_public_artifact_bytes)
                >> 20)
                .max(64)
                + 64,
        }
    }
}

/// An artifact produced by a job. Only `stored` ones are reported as
/// `JobResult.artifacts` (the server requires them to be uploaded).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedArtifact {
    pub name: String,
    pub digest: Digest,
    pub public: bool,
    pub stored: bool,
}

/// Fail-closed version binding for oracle requests (docs/PROTOCOL_UPGRADES.md
/// §3): the judge never runs a candidate on a request whose embedded
/// protocol version or chain id differs from the challenge's. Requests in the
/// `near-arena-request-v1` encoding start with
/// `str format ‖ str statement_id ‖ u32 protocol_version ‖ str chain_id`
/// (`str` = u32 LE length ‖ bytes); the pin checks that header before any
/// sandbox runs. A mismatch is a judge-side error (`ExecError::Infra`), never
/// a candidate verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequestPin {
    pub format: String,
    pub protocol_version: u32,
    pub chain_id: String,
}

impl RequestPin {
    pub const NEAR_REQUEST_V1: &'static str = "near-arena-request-v1";

    /// The pin for a challenge whose claim encoding is `near-arena-claim-v1`
    /// (`None` for other encodings, e.g. the toy demo challenge).
    pub fn from_challenge(c: &arena_types::ChallengeDefinition) -> Option<Self> {
        (c.claim_encoding.format == "near-arena-claim-v1").then(|| RequestPin {
            format: Self::NEAR_REQUEST_V1.into(),
            protocol_version: c.protocol_version,
            chain_id: c.chain_id.clone(),
        })
    }

    /// Check the request header; `Err` describes the mismatch.
    pub fn check(&self, request: &[u8]) -> Result<(), String> {
        fn take<'a>(b: &mut &'a [u8], n: usize) -> Result<&'a [u8], String> {
            if b.len() < n {
                return Err("request truncated inside the header".into());
            }
            let (h, t) = b.split_at(n);
            *b = t;
            Ok(h)
        }
        fn u32le(b: &mut &[u8]) -> Result<u32, String> {
            Ok(u32::from_le_bytes(take(b, 4)?.try_into().expect("4 bytes")))
        }
        fn bytes<'a>(b: &mut &'a [u8]) -> Result<&'a [u8], String> {
            let n = u32le(b)? as usize;
            take(b, n)
        }
        let mut b = request;
        let format = bytes(&mut b)?;
        if format != self.format.as_bytes() {
            return Err(format!(
                "request format {:?}, challenge expects {:?}",
                String::from_utf8_lossy(format),
                self.format
            ));
        }
        let _statement = bytes(&mut b)?;
        let pv = u32le(&mut b)?;
        if pv != self.protocol_version {
            return Err(format!(
                "request protocol_version {pv} != challenge protocol_version {}",
                self.protocol_version
            ));
        }
        let chain = bytes(&mut b)?;
        if chain != self.chain_id.as_bytes() {
            return Err(format!(
                "request chain_id {:?} != challenge chain_id {:?}",
                String::from_utf8_lossy(chain),
                self.chain_id
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::RequestPin;

    fn header(format: &str, statement: &str, pv: u32, chain: &str) -> Vec<u8> {
        let mut b = vec![];
        for s in [format, statement] {
            b.extend_from_slice(&(s.len() as u32).to_le_bytes());
            b.extend_from_slice(s.as_bytes());
        }
        b.extend_from_slice(&pv.to_le_bytes());
        b.extend_from_slice(&(chain.len() as u32).to_le_bytes());
        b.extend_from_slice(chain.as_bytes());
        b.extend_from_slice(&[7u8; 40]); // rest of the request
        b
    }

    #[test]
    fn request_pin_fails_closed_on_other_versions() {
        let pin = RequestPin {
            format: RequestPin::NEAR_REQUEST_V1.into(),
            protocol_version: 86,
            chain_id: "mainnet".into(),
        };
        let st = "near/pv86/receipt-transfer-batch/v0";
        pin.check(&header("near-arena-request-v1", st, 86, "mainnet"))
            .unwrap();
        for (bad, why) in [
            (
                header("near-arena-request-v1", st, 85, "mainnet"),
                "protocol_version 85",
            ),
            (
                header("near-arena-request-v1", st, 87, "mainnet"),
                "protocol_version 87",
            ),
            (
                header("near-arena-request-v1", st, 86, "testnet"),
                "chain_id",
            ),
            (header("near-arena-request-v2", st, 86, "mainnet"), "format"),
            (
                header("near-arena-request-v1", st, 86, "mainnet")[..30].to_vec(),
                "truncated",
            ),
            (vec![], "truncated"),
        ] {
            let e = pin.check(&bad).unwrap_err();
            assert!(e.contains(why), "{e}");
        }
    }
}
