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
