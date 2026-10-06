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
/// | `near-arena-claim-v3` | `near-arena-claim-v3` (the claim *is* the request) | `near/pv86/chunk-validation/v0` |
///
/// v3 (spec/claim-v3.md): there is no request file — the judge hands the
/// candidate the claim to prove as `request.bin`, and the expected claim is
/// that same byte string ([`RequestPin::check_case`]). `params.bin` is
/// `near-arena-params-v3` (`str format ‖ str statement ‖ u32 pv ‖ str
/// domain_id ‖ hash runtime_config_digest`, no chain id); the domain is the
/// `#<domain>` suffix of the challenge's `semantic_scope.name`.
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
    /// v3: `params.bin` domain id (`D0`, ...); `None` for v1/v2.
    pub domain: Option<String>,
}

impl RequestPin {
    pub const NEAR_REQUEST_V1: &'static str = "near-arena-request-v1";
    pub const NEAR_REQUEST_V2: &'static str = "near-arena-request-v2";
    pub const NEAR_STATEMENT_V1: &'static str = "near/pv86/receipt-transfer-batch/v0";
    pub const NEAR_STATEMENT_V2: &'static str = "near/pv86/receipt-transfer-batch/v1";
    pub const NEAR_PARAMS: &'static str = "near-arena-params-v1";
    pub const NEAR_CLAIM_V3: &'static str = "near-arena-claim-v3";
    pub const NEAR_STATEMENT_V3: &'static str = "near/pv86/chunk-validation/v0";
    pub const NEAR_PARAMS_V3: &'static str = "near-arena-params-v3";

    /// The pin for a challenge whose claim encoding is a NEAR encoding
    /// (`None` for other encodings, e.g. the toy demo challenge).
    pub fn from_challenge(c: &arena_types::ChallengeDefinition) -> Option<Self> {
        let (format, statement) = match c.claim_encoding.format.as_str() {
            "near-arena-claim-v1" => (Self::NEAR_REQUEST_V1, Self::NEAR_STATEMENT_V1),
            "near-arena-claim-v2" => (Self::NEAR_REQUEST_V2, Self::NEAR_STATEMENT_V2),
            "near-arena-claim-v3" => (Self::NEAR_CLAIM_V3, Self::NEAR_STATEMENT_V3),
            _ => return None,
        };
        // v3: the domain is the `#<domain>` suffix of the scope name; a v3
        // challenge whose scope names no domain matches no params.bin.
        let domain = (format == Self::NEAR_CLAIM_V3).then(|| {
            c.semantic_scope
                .name
                .rsplit_once('#')
                .map(|(_, d)| d.to_string())
                .unwrap_or_default()
        });
        Some(RequestPin {
            format: format.into(),
            claim_format: c.claim_encoding.format.clone(),
            statement_id: statement.into(),
            protocol_version: c.protocol_version,
            chain_id: c.chain_id.clone(),
            domain,
        })
    }

    /// v3: the request is the claim itself.
    pub fn request_is_claim(&self) -> bool {
        self.domain.is_some()
    }

    /// The full pin of one oracle case: request header, expected-claim
    /// header and, for v3, `request == expected_claim` (the judge never asks
    /// a v3 prover for a claim other than the one it hands over). A
    /// rejection case (no expected claim) is checked on its request only.
    pub fn check_case(&self, request: &[u8], expected_claim: Option<&[u8]>) -> Result<(), String> {
        self.check(request)?;
        if let Some(c) = expected_claim {
            self.check_claim(c)?;
            if self.request_is_claim() && c != request {
                return Err("v3 case: request.bin differs from the expected claim (the claim is the request)".into());
            }
        }
        Ok(())
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
        if let Some(domain) = &self.domain {
            return self.check_params_v3(params, domain, runtime_config);
        }
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

impl RequestPin {
    /// `near-arena-params-v3` (spec/claim-v3.md §4): `str format ‖ str
    /// statement ‖ u32 pv ‖ str domain_id ‖ hash runtime_config_digest_v3`.
    fn check_params_v3(
        &self,
        params: &[u8],
        domain: &str,
        runtime_config: &Digest,
    ) -> Result<(), String> {
        let mut p = params;
        fn take2<'a>(p: &mut &'a [u8], n: usize) -> Result<&'a [u8], String> {
            if p.len() < n {
                return Err("params truncated".into());
            }
            let (h, t) = p.split_at(n);
            *p = t;
            Ok(h)
        }
        fn bytes<'a>(p: &mut &'a [u8]) -> Result<&'a [u8], String> {
            let n = u32::from_le_bytes(take2(p, 4)?.try_into().expect("4 bytes")) as usize;
            take2(p, n)
        }
        let f = bytes(&mut p)?;
        if f != Self::NEAR_PARAMS_V3.as_bytes() {
            return Err(format!(
                "params format {:?}, challenge expects {:?}",
                String::from_utf8_lossy(f),
                Self::NEAR_PARAMS_V3
            ));
        }
        let st = bytes(&mut p)?;
        if st != self.statement_id.as_bytes() {
            return Err(format!(
                "params statement_id {:?}, challenge expects {:?}",
                String::from_utf8_lossy(st),
                self.statement_id
            ));
        }
        let pv = u32::from_le_bytes(take2(&mut p, 4)?.try_into().expect("4 bytes"));
        if pv != self.protocol_version {
            return Err(format!(
                "params protocol_version {pv} != challenge protocol_version {}",
                self.protocol_version
            ));
        }
        let d = bytes(&mut p)?;
        if d != domain.as_bytes() {
            return Err(format!(
                "params domain_id {:?} != challenge domain {domain:?}",
                String::from_utf8_lossy(d)
            ));
        }
        let got: String = take2(&mut p, 32)?
            .iter()
            .map(|x| format!("{x:02x}"))
            .collect();
        if !p.is_empty() {
            return Err("params: trailing bytes".into());
        }
        if got != runtime_config.hex() {
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
            domain: None,
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

    /// A04 (v3): the v3 pin accepts v3 claims (request = claim), v3 params
    /// (domain D0, runtime-config digest) and nothing of v1/v2; a request
    /// that differs from the expected claim, a foreign domain, protocol
    /// version or chain id is refused.
    #[test]
    fn v3_pin_claim_is_request_and_params_carry_the_domain() {
        let v3 = chal("challenges/drafts/near-chunk-validation-d0.draft.json");
        let v1 = chal("challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json");
        let p3 = RequestPin::from_challenge(&v3).unwrap();
        assert_eq!(p3.format, RequestPin::NEAR_CLAIM_V3);
        assert_eq!(p3.statement_id, RequestPin::NEAR_STATEMENT_V3);
        assert_eq!(p3.domain.as_deref(), Some("D0"));
        assert!(p3.request_is_claim());
        let dir = "oracle/fixtures/v3/arena-public";
        let c = fixture(&format!("{dir}/cases/00-h10024-s0/request.bin"));
        let k = fixture(&format!("{dir}/cases/00-h10024-s0/expected_claim.bin"));
        let rj = fixture(&format!(
            "{dir}/rejections/00-h10024-s3-hdr.prev_state_root/request.bin"
        ));
        let pa = fixture(&format!("{dir}/params.bin"));
        p3.check_case(&c, Some(&k)).unwrap();
        p3.check_case(&rj, None).unwrap();
        p3.check_params(&pa, &v3.runtime_config_digest).unwrap();
        // the claim is the request: a different expected claim is refused
        let other = fixture(&format!("{dir}/cases/00-h10006-s3/expected_claim.bin"));
        assert!(p3
            .check_case(&c, Some(&other))
            .unwrap_err()
            .contains("request.bin differs"));
        // v1 artifacts never pass the v3 pin and vice versa
        let c1 = "oracle/fixtures/public/cases/example-tierA";
        assert!(p3
            .check(&fixture(&format!("{c1}/request.bin")))
            .unwrap_err()
            .contains("format"));
        let p1 = RequestPin::from_challenge(&v1).unwrap();
        assert!(p1.check(&c).unwrap_err().contains("format"));
        assert!(p1
            .check_params(&pa, &v1.runtime_config_digest)
            .unwrap_err()
            .contains("format"));
        assert!(p3
            .check_params(
                &fixture("oracle/fixtures/public/params.bin"),
                &v3.runtime_config_digest
            )
            .unwrap_err()
            .contains("format"));
        // wrong domain / digest / chain / protocol version
        let mut d1 = v3.clone();
        d1.semantic_scope.name = "near/pv86/chunk-validation/v0#D1".into();
        let e = RequestPin::from_challenge(&d1)
            .unwrap()
            .check_params(&pa, &v3.runtime_config_digest);
        assert!(e.unwrap_err().contains("domain_id"));
        let e = p3.check_params(&pa, &v1.runtime_config_digest);
        assert!(e.unwrap_err().contains("runtime_config_digest"));
        let mut ch = v3.clone();
        ch.chain_id = "mainnet".into();
        let e = RequestPin::from_challenge(&ch).unwrap().check(&c);
        assert!(e.unwrap_err().contains("chain_id"));
        let mut pv = v3.clone();
        pv.protocol_version = 87;
        let e = RequestPin::from_challenge(&pv).unwrap().check(&c);
        assert!(e.unwrap_err().contains("protocol_version"));
        let mut trailing = pa.clone();
        trailing.push(0);
        assert!(p3
            .check_params(&trailing, &v3.runtime_config_digest)
            .unwrap_err()
            .contains("trailing"));
    }
}
