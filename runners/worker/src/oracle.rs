//! Judge-side oracles: what must be proved, and the expected claim for each
//! request (CONTRACTS §4: the judge computes `expected_claim(request)`
//! itself; a candidate claim that differs is `CLAIM_MISMATCH`).
//!
//! An [`Oracle`] is selected by the challenge's `claim_encoding.format`.
//! Public fixtures are located on disk **by TreeDigest**: the worker indexes
//! the directories listed in `ARENA_FIXTURES_DIRS` and only uses one whose
//! digest equals `workload_suite.public_fixtures`.
//!
//! The spec-oracle lane will provide the NEAR oracle (requests, witnesses,
//! expected claims as files); it plugs in by implementing [`Oracle`].
//! Workload sampling here uses public seeds derived from the challenge,
//! package digest and class (`derive_seed("workload", ...)`); the
//! season-secret HMAC of docs/BENCHMARK_SPEC.md §11.1 is not wired yet.

use arena_measure::stats::{derive_seed, SplitMix64};
use arena_types::{ChallengeDefinition, Digest};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// One proving request with the judge's expected result. Bytes are held
/// in memory (requests/witnesses/claims are bounded by `claim_encoding`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Case {
    pub id: String,
    pub request: Vec<u8>,
    pub witness: Vec<u8>,
    pub expected_claim: Vec<u8>,
    /// Public cases may be named in reports; others (sampled, held-out) not.
    pub public: bool,
}

#[derive(Debug, thiserror::Error)]
pub enum OracleError {
    /// No oracle for this challenge on this worker: gates stay UNKNOWN.
    #[error("no oracle available: {0}")]
    Unavailable(String),
    /// Judge-side inconsistency (corrupt fixtures, ...): infra error.
    #[error("oracle error: {0}")]
    Broken(String),
}

pub trait Oracle: Send + Sync {
    /// `claim_encoding.format` handled by this oracle.
    fn format(&self) -> &str;
    /// Conformance suite: public fixtures plus `sampled` judge-sampled cases.
    fn conformance_cases(
        &self,
        chal: &ChallengeDefinition,
        fixtures: Option<&Path>,
        seed_parts: &[&str],
        sampled: usize,
    ) -> Result<Vec<Case>, OracleError>;
    /// `n` judge-sampled cases from the generator of workload class `class_id`.
    fn sample(&self, chal: &ChallengeDefinition, class_id: &str, seed_parts: &[&str], n: usize) -> Result<Vec<Case>, OracleError>;
    /// `approved_params.bin` handed to the judge-run `prepare` (empty unless
    /// the claim encoding defines one).
    fn approved_params(&self, _chal: &ChallengeDefinition, _fixtures: Option<&Path>) -> Result<Vec<u8>, OracleError> {
        Ok(vec![])
    }
}

/// Oracle registry + fixture index.
#[derive(Default)]
pub struct Oracles {
    oracles: Vec<Box<dyn Oracle>>,
    fixtures: HashMap<Digest, PathBuf>,
}

impl Oracles {
    /// Built-in oracles (currently `demo-toy-arith-v1`).
    pub fn builtin() -> Self {
        Oracles { oracles: vec![Box::new(ToyArith)], fixtures: HashMap::new() }
    }

    /// Built-ins plus the NEAR oracle when its binary and generator specs
    /// are configured.
    pub fn with_near(mut self, oracle_bin: PathBuf, generators_dir: &Path) -> Result<Self, String> {
        self.oracles.push(Box::new(NearOracle::new(oracle_bin, generators_dir)?));
        Ok(self)
    }

    pub fn register(&mut self, o: Box<dyn Oracle>) {
        self.oracles.push(o);
    }

    /// Index a fixtures directory by its TreeDigest.
    pub fn add_fixtures_dir(&mut self, dir: &Path) -> Result<Digest, String> {
        let t = arena_archive::tree_from_dir(dir, &arena_archive::Limits::default()).map_err(|e| format!("{}: {e}", dir.display()))?;
        let d = t.digest();
        self.fixtures.insert(d.clone(), dir.to_path_buf());
        Ok(d)
    }

    /// Fixtures for a challenge, re-verified against the committed digest.
    pub fn fixtures_for(&self, chal: &ChallengeDefinition) -> Result<Option<PathBuf>, OracleError> {
        let want = &chal.workload_suite.public_fixtures;
        let Some(dir) = self.fixtures.get(want) else { return Ok(None) };
        let t = arena_archive::tree_from_dir(dir, &arena_archive::Limits::default()).map_err(|e| OracleError::Broken(e.to_string()))?;
        if &t.digest() != want {
            return Err(OracleError::Broken(format!("fixtures dir {} changed since indexing", dir.display())));
        }
        Ok(Some(dir.clone()))
    }

    pub fn get(&self, chal: &ChallengeDefinition) -> Result<&dyn Oracle, OracleError> {
        let f = &chal.claim_encoding.format;
        self.oracles
            .iter()
            .find(|o| o.format() == f)
            .map(|b| b.as_ref())
            .ok_or_else(|| OracleError::Unavailable(format!("no oracle for claim encoding {f:?} on this worker")))
    }
}

fn hex_decode(s: &str) -> Result<Vec<u8>, String> {
    if !s.len().is_multiple_of(2) || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!("bad hex {s:?}"));
    }
    Ok((0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect())
}

/// `demo-toy-arith-v1` (challenges/demo/toy-arithmetic/SPEC.md):
/// request `a‖b`, empty witness, claim `a‖b‖(a·b mod 2^64)`, u64 LE.
pub struct ToyArith;

impl ToyArith {
    pub fn expected_claim(request: &[u8]) -> Option<Vec<u8>> {
        if request.len() != 16 {
            return None;
        }
        let a = u64::from_le_bytes(request[..8].try_into().unwrap());
        let b = u64::from_le_bytes(request[8..].try_into().unwrap());
        let mut c = request.to_vec();
        c.extend_from_slice(&a.wrapping_mul(b).to_le_bytes());
        Some(c)
    }

    fn case(id: String, a: u64, b: u64, public: bool) -> Case {
        let mut request = a.to_le_bytes().to_vec();
        request.extend_from_slice(&b.to_le_bytes());
        let expected_claim = Self::expected_claim(&request).expect("16 bytes");
        Case { id, request, witness: vec![], expected_claim, public }
    }

    fn bits(chal: &ChallengeDefinition, class_id: &str) -> Result<u32, OracleError> {
        // Generators are identified by digest in the challenge; the two demo
        // generators differ only in the operand width.
        let class = chal
            .workload_suite
            .classes
            .iter()
            .find(|c| c.id == class_id)
            .ok_or_else(|| OracleError::Broken(format!("unknown class {class_id:?}")))?;
        Ok(match class.id.as_str() {
            "toy-small" => 32,
            "toy-large" => 64,
            _ if class.description.contains("2^32") => 32,
            _ => 64,
        })
    }
}

impl Oracle for ToyArith {
    fn format(&self) -> &str {
        "demo-toy-arith-v1"
    }

    fn conformance_cases(
        &self,
        chal: &ChallengeDefinition,
        fixtures: Option<&Path>,
        seed_parts: &[&str],
        sampled: usize,
    ) -> Result<Vec<Case>, OracleError> {
        let mut out = vec![];
        if let Some(dir) = fixtures {
            let mut names: Vec<_> = std::fs::read_dir(dir)
                .map_err(|e| OracleError::Broken(e.to_string()))?
                .filter_map(|e| e.ok()?.file_name().into_string().ok())
                .filter(|n| n.ends_with(".json"))
                .collect();
            names.sort();
            for n in names {
                let v: serde_json::Value = serde_json::from_slice(&std::fs::read(dir.join(&n)).map_err(|e| OracleError::Broken(e.to_string()))?)
                    .map_err(|e| OracleError::Broken(format!("{n}: {e}")))?;
                let req = hex_decode(v["request_hex"].as_str().unwrap_or("")).map_err(OracleError::Broken)?;
                let want = Self::expected_claim(&req).ok_or_else(|| OracleError::Broken(format!("{n}: bad request length")))?;
                // The judge computes the claim itself; the fixture's copy must agree.
                if let Some(h) = v["expected_claim_hex"].as_str() {
                    if hex_decode(h).map_err(OracleError::Broken)? != want {
                        return Err(OracleError::Broken(format!("{n}: fixture claim disagrees with the judge's oracle")));
                    }
                }
                out.push(Case { id: format!("fixture/{}", n.trim_end_matches(".json")), request: req, witness: vec![], expected_claim: want, public: true });
            }
        }
        let per_class = sampled.div_ceil(chal.workload_suite.classes.len().max(1));
        for c in &chal.workload_suite.classes {
            out.extend(self.sample(chal, &c.id, seed_parts, per_class)?);
        }
        Ok(out)
    }

    fn sample(&self, chal: &ChallengeDefinition, class_id: &str, seed_parts: &[&str], n: usize) -> Result<Vec<Case>, OracleError> {
        let bits = Self::bits(chal, class_id)?;
        let mut parts = vec![class_id];
        parts.extend_from_slice(seed_parts);
        let seed = derive_seed("workload", &parts).map_err(OracleError::Broken)?;
        let mut rng = SplitMix64::new(seed);
        let mask = if bits >= 64 { u64::MAX } else { (1u64 << bits) - 1 };
        Ok((0..n)
            .map(|i| {
                let a = rng.next_u64() & mask;
                let b = rng.next_u64() & mask;
                Self::case(format!("{class_id}/{i}"), a, b, false)
            })
            .collect())
    }
}

/// `near-arena-claim-v1` (spec/near-transfer-receipt-v1.md): requests,
/// witnesses and expected claims are produced by the governed oracle
/// (`near-arena-oracle`, which executes the pinned nearcore runtime). Public
/// fixtures come from the digest-matched fixtures dir
/// (`cases/<name>/{request,witness,expected_claim}.bin`, `params.bin`);
/// sampled batches run `near-arena-oracle gen` with the arguments of the
/// class's generator spec (located by the digest the challenge commits to)
/// and a judge-derived seed.
pub struct NearOracle {
    bin: PathBuf,
    generators: HashMap<Digest, serde_json::Value>,
}

impl NearOracle {
    pub fn new(bin: PathBuf, generators_dir: &Path) -> Result<Self, String> {
        let mut generators = HashMap::new();
        for e in std::fs::read_dir(generators_dir).map_err(|e| format!("{}: {e}", generators_dir.display()))?.flatten() {
            let p = e.path();
            if p.extension().is_some_and(|x| x == "json") {
                let v: serde_json::Value = serde_json::from_slice(&std::fs::read(&p).map_err(|e| e.to_string())?).map_err(|e| format!("{}: {e}", p.display()))?;
                let d = arena_types::sha256_digest(&v).map_err(|e| e.to_string())?;
                generators.insert(d, v);
            }
        }
        Ok(NearOracle { bin, generators })
    }

    fn read_cases(dir: &Path, public: bool, prefix: &str) -> Result<Vec<Case>, OracleError> {
        let mut names: Vec<String> = std::fs::read_dir(dir)
            .map_err(|e| OracleError::Broken(format!("{}: {e}", dir.display())))?
            .flatten()
            .filter_map(|e| e.file_name().into_string().ok())
            .collect();
        names.sort();
        let mut out = vec![];
        for n in names {
            let d = dir.join(&n);
            // Out-of-domain cases carry no expected claim: never issued.
            let Ok(expected_claim) = std::fs::read(d.join("expected_claim.bin")) else { continue };
            let rd = |f: &str| std::fs::read(d.join(f)).map_err(|e| OracleError::Broken(format!("{n}/{f}: {e}")));
            out.push(Case { id: format!("{prefix}{n}"), request: rd("request.bin")?, witness: rd("witness.bin")?, expected_claim, public });
        }
        Ok(out)
    }
}

impl Oracle for NearOracle {
    fn format(&self) -> &str {
        "near-arena-claim-v1"
    }

    fn conformance_cases(
        &self,
        chal: &ChallengeDefinition,
        fixtures: Option<&Path>,
        seed_parts: &[&str],
        sampled: usize,
    ) -> Result<Vec<Case>, OracleError> {
        let mut out = match fixtures {
            Some(f) => Self::read_cases(&f.join("cases"), true, "fixture/")?,
            None => vec![],
        };
        let per_class = sampled.div_ceil(chal.workload_suite.classes.len().max(1));
        for c in &chal.workload_suite.classes {
            out.extend(self.sample(chal, &c.id, seed_parts, per_class)?);
        }
        Ok(out)
    }

    fn sample(&self, chal: &ChallengeDefinition, class_id: &str, seed_parts: &[&str], n: usize) -> Result<Vec<Case>, OracleError> {
        if n == 0 {
            return Ok(vec![]);
        }
        let class = chal
            .workload_suite
            .classes
            .iter()
            .find(|c| c.id == class_id)
            .ok_or_else(|| OracleError::Broken(format!("unknown class {class_id:?}")))?;
        let spec = self
            .generators
            .get(&class.generator)
            .ok_or_else(|| OracleError::Unavailable(format!("no generator spec with digest {} on this worker", class.generator)))?;
        let args: Vec<String> = spec["args"].as_array().map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect()).unwrap_or_default();
        if !args.iter().any(|a| a == "--fixtures-layout") {
            return Err(OracleError::Broken("generator spec must use --fixtures-layout".into()));
        }
        let mut parts = vec![class_id];
        parts.extend_from_slice(seed_parts);
        let seed = derive_seed("workload", &parts).map_err(OracleError::Broken)?;
        let out_dir = std::env::temp_dir().join(format!("near-oracle-{}-{seed}-{n}", std::process::id()));
        let _ = std::fs::remove_dir_all(&out_dir);
        let o = std::process::Command::new(&self.bin)
            .arg("gen")
            .args(["--seed", &seed.to_string(), "--valid", &n.to_string(), "--invalid", "0", "--out"])
            .arg(&out_dir)
            .args(&args)
            .output()
            .map_err(|e| OracleError::Broken(format!("near-arena-oracle: {e}")))?;
        if !o.status.success() {
            return Err(OracleError::Broken(format!("near-arena-oracle gen failed: {}", String::from_utf8_lossy(&o.stderr))));
        }
        let cases = Self::read_cases(&out_dir.join("cases"), false, &format!("{class_id}/"));
        let _ = std::fs::remove_dir_all(&out_dir);
        let cases = cases?;
        if cases.is_empty() {
            return Err(OracleError::Broken(format!("generator produced no in-domain cases for {class_id}")));
        }
        Ok(cases)
    }

    fn approved_params(&self, _chal: &ChallengeDefinition, fixtures: Option<&Path>) -> Result<Vec<u8>, OracleError> {
        let f = fixtures.ok_or_else(|| OracleError::Unavailable("near-arena-claim-v1 needs the public fixtures (params.bin)".into()))?;
        std::fs::read(f.join("params.bin")).map_err(|e| OracleError::Broken(format!("params.bin: {e}")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn toy_claim() {
        let mut r = 3u64.to_le_bytes().to_vec();
        r.extend_from_slice(&u64::MAX.to_le_bytes());
        let c = ToyArith::expected_claim(&r).unwrap();
        assert_eq!(&c[16..], &3u64.wrapping_mul(u64::MAX).to_le_bytes());
        assert!(ToyArith::expected_claim(&r[..15]).is_none());
    }
}
