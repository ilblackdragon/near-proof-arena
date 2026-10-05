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

/// Fail-closed version binding for oracle requests, expected claims and
/// approved parameters (docs/PROTOCOL_UPGRADES.md §3): the judge never runs a
/// candidate on a request whose encoding, statement (scope), protocol version
/// or chain id differs from the challenge's. NEAR requests, claims and
/// `params.bin` start with
/// `str format ‖ str statement_id ‖ u32 protocol_version ‖ str chain_id`
/// (`str` = u32 LE length ‖ bytes); the pin checks that header before any
/// sandbox runs. A mismatch is a judge-side error (`ExecError::Infra`), never
/// a candidate verdict.
///
/// | claim encoding | request format | statement id |
/// |---|---|---|
/// | `near-arena-claim-v1` | `near-arena-request-v1` | `near/pv86/receipt-transfer-batch/v0` |
/// | `near-arena-claim-v2` | `near-arena-request-v2` | `near/pv86/receipt-transfer-batch/v1` |
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequestPin {
    /// Request encoding (`near-arena-request-vN`).
    pub format: String,
    /// Claim encoding (= `claim_encoding.format`).
    pub claim_format: String,
    /// Statement id (scope) of the claim encoding.
    pub statement_id: String,
    pub protocol_version: u32,
    pub chain_id: String,
}

impl RequestPin {
    pub const NEAR_REQUEST_V1: &'static str = "near-arena-request-v1";
    pub const NEAR_REQUEST_V2: &'static str = "near-arena-request-v2";
    pub const NEAR_STATEMENT_V1: &'static str = "near/pv86/receipt-transfer-batch/v0";
    pub const NEAR_STATEMENT_V2: &'static str = "near/pv86/receipt-transfer-batch/v1";
    pub const NEAR_PARAMS: &'static str = "near-arena-params-v1";

    /// The pin for a challenge whose claim encoding is a NEAR encoding
    /// (`None` for other encodings, e.g. the toy demo challenge).
    pub fn from_challenge(c: &arena_types::ChallengeDefinition) -> Option<Self> {
        let (format, statement) = match c.claim_encoding.format.as_str() {
            "near-arena-claim-v1" => (Self::NEAR_REQUEST_V1, Self::NEAR_STATEMENT_V1),
            "near-arena-claim-v2" => (Self::NEAR_REQUEST_V2, Self::NEAR_STATEMENT_V2),
            _ => return None,
        };
        Some(RequestPin {
            format: format.into(),
            claim_format: c.claim_encoding.format.clone(),
            statement_id: statement.into(),
            protocol_version: c.protocol_version,
            chain_id: c.chain_id.clone(),
        })
    }

    /// Check a `format ‖ statement ‖ pv ‖ chain` header; returns the rest.
    fn header<'a>(&self, what: &str, b: &'a [u8], format: &str) -> Result<&'a [u8], String> {
        fn take<'a>(b: &mut &'a [u8], n: usize) -> Result<&'a [u8], String> {
            if b.len() < n {
                return Err("truncated inside the header".into());
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
        let mut b = b;
        let e = |m: String| format!("{what} {m}");
        let f = bytes(&mut b).map_err(e)?;
        if f != format.as_bytes() {
            return Err(format!(
                "{what} format {:?}, challenge expects {format:?}",
                String::from_utf8_lossy(f)
            ));
        }
        let st = bytes(&mut b).map_err(e)?;
        if st != self.statement_id.as_bytes() {
            return Err(format!(
                "{what} statement_id {:?}, challenge expects {:?}",
                String::from_utf8_lossy(st),
                self.statement_id
            ));
        }
        let pv = u32le(&mut b).map_err(e)?;
        if pv != self.protocol_version {
            return Err(format!(
                "{what} protocol_version {pv} != challenge protocol_version {}",
                self.protocol_version
            ));
        }
        let chain = bytes(&mut b).map_err(e)?;
        if chain != self.chain_id.as_bytes() {
            return Err(format!(
                "{what} chain_id {:?} != challenge chain_id {:?}",
                String::from_utf8_lossy(chain),
                self.chain_id
            ));
        }
        Ok(b)
    }

    /// Check the request header; `Err` describes the mismatch.
    pub fn check(&self, request: &[u8]) -> Result<(), String> {
        self.header("request", request, &self.format).map(|_| ())
    }

    /// Check the header of a judge-computed expected claim.
    pub fn check_claim(&self, claim: &[u8]) -> Result<(), String> {
        self.header("expected claim", claim, &self.claim_format)
            .map(|_| ())
    }

    /// Check `params.bin` (`near-arena-params-v1`): the header, then exactly
    /// the challenge's 32-byte `runtime_config_digest`.
    pub fn check_params(&self, params: &[u8], runtime_config: &Digest) -> Result<(), String> {
        let rest = self.header("params", params, Self::NEAR_PARAMS)?;
        let want = runtime_config.hex();
        let got: String = rest.iter().map(|x| format!("{x:02x}")).collect();
        if got != want {
            return Err(format!(
                "params runtime_config_digest sha256:{got} != challenge runtime_config_digest {runtime_config}"
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
            claim_format: "near-arena-claim-v1".into(),
            statement_id: RequestPin::NEAR_STATEMENT_V1.into(),
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
                header(
                    "near-arena-request-v1",
                    RequestPin::NEAR_STATEMENT_V2,
                    86,
                    "mainnet",
                ),
                "statement_id",
            ),
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

    fn fixture(rel: &str) -> Vec<u8> {
        std::fs::read(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join(rel),
        )
        .unwrap()
    }

    fn chal(rel: &str) -> arena_types::ChallengeDefinition {
        serde_json::from_slice(&fixture(rel)).unwrap()
    }

    /// A04: the v2 pin accepts v2 requests/claims/params only, the v1 pin v1
    /// only (encoding, statement id, protocol version, chain id).
    #[test]
    fn v1_and_v2_pins_reject_each_others_cases() {
        let v1 = chal("challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json");
        let v2 = chal("challenges/drafts/near-transfer-receipt-v2.draft.json");
        let p1 = RequestPin::from_challenge(&v1).unwrap();
        let p2 = RequestPin::from_challenge(&v2).unwrap();
        assert_eq!(p2.format, RequestPin::NEAR_REQUEST_V2);
        assert_eq!(p2.statement_id, RequestPin::NEAR_STATEMENT_V2);
        let c1 = "oracle/fixtures/public/cases/example-tierA";
        let c2 = "oracle/fixtures/v2/public/cases/example-v2-tierA";
        let (r1, r2) = (
            fixture(&format!("{c1}/request.bin")),
            fixture(&format!("{c2}/request.bin")),
        );
        let (k1, k2) = (
            fixture(&format!("{c1}/expected_claim.bin")),
            fixture(&format!("{c2}/expected_claim.bin")),
        );
        let (pa1, pa2) = (
            fixture("oracle/fixtures/public/params.bin"),
            fixture("oracle/fixtures/v2/public/params.bin"),
        );
        p1.check(&r1).unwrap();
        p1.check_claim(&k1).unwrap();
        p1.check_params(&pa1, &v1.runtime_config_digest).unwrap();
        p2.check(&r2).unwrap();
        p2.check_claim(&k2).unwrap();
        p2.check_params(&pa2, &v2.runtime_config_digest).unwrap();
        assert!(p2.check(&r1).unwrap_err().contains("format"));
        assert!(p1.check(&r2).unwrap_err().contains("format"));
        assert!(p2.check_claim(&k1).unwrap_err().contains("format"));
        assert!(p1.check_claim(&k2).unwrap_err().contains("format"));
        assert!(p2
            .check_params(&pa1, &v2.runtime_config_digest)
            .unwrap_err()
            .contains("statement_id"));
        assert!(p2
            .check_params(&pa2, &v1.runtime_config_digest)
            .unwrap_err()
            .contains("runtime_config_digest"));
        // The v2 rejection fixture for a foreign protocol version.
        let bad = fixture(
            "oracle/fixtures/v2/rejection/cases/s20261003-y12-wrong_protocol_version/request.bin",
        );
        assert!(p2.check(&bad).unwrap_err().contains("protocol_version"));
        // Non-NEAR encodings carry no pin.
        let mut toy = v2.clone();
        toy.claim_encoding.format = "demo-toy-arith-v1".into();
        assert!(RequestPin::from_challenge(&toy).is_none());
    }
}
