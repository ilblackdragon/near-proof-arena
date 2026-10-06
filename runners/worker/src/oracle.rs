//! Judge-side oracles: what must be proved, and the expected claim for each
//! request (CONTRACTS §4: the judge computes `expected_claim(request)`
//! itself; a candidate claim that differs is `CLAIM_MISMATCH`).
//!
//! An [`Oracle`] is selected by the challenge's `claim_encoding.format`
//! (exact match; `near-arena-claim-v1`, `near-arena-claim-v2` and
//! `near-arena-claim-v3` are separate registrations, so an oracle never
//! serves a challenge of another encoding).
//!
//! **Rejection cases** ([`Oracles::rejection_suite`], v3): judge-held
//! (claim, witness) pairs whose expected verdict is *reject* — nearcore's own
//! validator rejects them, or the honest chunk lies outside the challenge's
//! domain. CONFORMANCE runs the candidate's `prove` on each and `verify` on
//! whatever it emits; an accepted proof of such a claim is a counterexample
//! to soundness (`COUNTEREXAMPLE_FOUND`).
//!
//! Conformance suites are assembled by [`Oracles::conformance_suite`], which
//! fails closed (audit A06):
//!
//! * **Public fixtures** are located on disk by TreeDigest: the worker
//!   indexes the directories listed in `ARENA_FIXTURES_DIRS` and only uses one
//!   whose digest equals `workload_suite.public_fixtures`. A challenge that
//!   pins a (non-zero) fixtures digest the worker cannot supply is an
//!   infrastructure error naming the pin, never a run on generated cases only.
//! * **Coverage**: every workload class must contribute at least
//!   `max(1, ceil(samples / classes))` judge-sampled cases, and a pinned
//!   fixture set must contain at least one in-domain case.
//! * **Sampling seeds** ([`SeedCtx`]): with a season secret
//!   (`ARENA_SEASON_SECRET_FILE`), `first 8 bytes BE of HMAC-SHA256(secret,
//!   "near-arena-workload-sample-v1|" challenge_id "|" package_digest "|"
//!   class)` exactly as docs/BENCHMARK_SPEC.md §11.1 and
//!   `benchmarks/arena_bench/seeds.py`; without one, the public
//!   `derive_seed("workload", ...)` (reported as such in the gate summary).
//! * **Held-out sets** (`workload_suite.heldout_commitment`): judge-only
//!   directories (`ARENA_HELDOUT_DIRS`) indexed by TreeDigest. When the worker
//!   has held-out dirs configured, a committed set that is missing or whose
//!   digest differs is an infrastructure error. Held-out cases are never
//!   public: their ids, sizes and failure details stay out of summaries (RT-04).

use arena_measure::stats::{derive_seed, SplitMix64};
use arena_types::{ChallengeDefinition, Digest};
use sha2::{Digest as _, Sha256};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

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
    /// Workload class of a sampled or held-out case (`None` for fixtures).
    pub class: Option<String>,
}

#[derive(Debug, thiserror::Error)]
pub enum OracleError {
    /// No oracle for this challenge on this worker: gates stay UNKNOWN.
    #[error("no oracle available: {0}")]
    Unavailable(String),
    /// Judge-side inconsistency (corrupt or missing pinned fixtures, held-out
    /// digest mismatch, ...): infra error.
    #[error("oracle error: {0}")]
    Broken(String),
    /// The suite does not meet the challenge's minimum coverage: infra
    /// error (fail closed; never a PASS on a thinner suite).
    #[error("fail-closed: insufficient conformance coverage: {0}")]
    Coverage(String),
}

pub trait Oracle: Send + Sync {
    /// `claim_encoding.format` handled by this oracle.
    fn format(&self) -> &str;
    /// The in-domain cases of a digest-verified public fixtures dir.
    fn fixture_cases(
        &self,
        chal: &ChallengeDefinition,
        dir: &Path,
    ) -> Result<Vec<Case>, OracleError>;
    /// `n` judge-sampled cases from the generator of workload class `class_id`
    /// (seeded by [`SeedCtx::class_seed`]); each carries `class = class_id`.
    fn sample(
        &self,
        chal: &ChallengeDefinition,
        class_id: &str,
        seeds: &SeedCtx,
        n: usize,
    ) -> Result<Vec<Case>, OracleError>;
    /// The held-out cases of class `class_id` from a digest-verified held-out
    /// dir (never public).
    fn heldout_cases(
        &self,
        _chal: &ChallengeDefinition,
        _dir: &Path,
        _class_id: &str,
    ) -> Result<Vec<Case>, OracleError> {
        Err(OracleError::Broken(format!(
            "held-out sets are not supported for {}",
            self.format()
        )))
    }
    /// Cases the candidate must NOT get accepted (expected verdict reject):
    /// from the public fixtures (`fixtures`), `n` freshly judge-sampled ones
    /// and, with `heldout`, `n` seed-selected held-out ones (never public).
    /// Empty for encodings without rejection oracles.
    fn rejection_cases(
        &self,
        _chal: &ChallengeDefinition,
        _fixtures: Option<&Path>,
        _heldout: Option<&Path>,
        _seeds: &SeedCtx,
        _n: usize,
    ) -> Result<RejectionSet, OracleError> {
        Ok(RejectionSet::default())
    }
    /// `approved_params.bin` handed to the judge-run `prepare` (empty unless
    /// the claim encoding defines one).
    fn approved_params(
        &self,
        _chal: &ChallengeDefinition,
        _fixtures: Option<&Path>,
    ) -> Result<Vec<u8>, OracleError> {
        Ok(vec![])
    }
}

/// The season secret of docs/BENCHMARK_SPEC.md §11.2: judge-only, never sent
/// to a sandbox, never logged (`Debug` prints only the public commitment).
pub struct SeasonSecret {
    key: Vec<u8>,
    commitment: String,
}

impl std::fmt::Debug for SeasonSecret {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SeasonSecret(<redacted>, {})", self.commitment)
    }
}

pub const SECRET_COMMIT_DOMAIN: &[u8] = b"near-arena-secret-commit-v1\0";
pub const SAMPLING_DOMAIN: &str = "near-arena-workload-sample-v1";

fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    let mut k0 = [0u8; 64];
    if key.len() > 64 {
        k0[..32].copy_from_slice(&Sha256::digest(key));
    } else {
        k0[..key.len()].copy_from_slice(key);
    }
    let pad = |b: u8| k0.iter().map(|k| k ^ b).collect::<Vec<u8>>();
    let inner = Sha256::new()
        .chain_update(pad(0x36))
        .chain_update(msg)
        .finalize();
    Sha256::new()
        .chain_update(pad(0x5c))
        .chain_update(inner)
        .finalize()
        .into()
}

fn seed_part_ok(p: &str) -> bool {
    !p.is_empty() && p.bytes().all(|b| (0x21..=0x7e).contains(&b) && b != b'|')
}

impl SeasonSecret {
    /// At least 32 secret bytes.
    pub fn from_bytes(key: Vec<u8>) -> Result<Self, String> {
        if key.len() < 32 {
            return Err("season secret must be at least 32 bytes".into());
        }
        let commitment = format!(
            "sha256:{}",
            hex_encode(
                &Sha256::new()
                    .chain_update(SECRET_COMMIT_DOMAIN)
                    .chain_update(&key)
                    .finalize()
            )
        );
        Ok(SeasonSecret { key, commitment })
    }

    /// Load the judge-only secret file: the secret as hex (≥ 64 hex digits,
    /// surrounding whitespace ignored). The file must not be group/other
    /// accessible. If `expected_commit` is given (the commitment governance
    /// published for the season), it must equal the file's commitment.
    pub fn from_file(path: &Path, expected_commit: Option<&str>) -> Result<Self, String> {
        use std::os::unix::fs::PermissionsExt;
        let meta = std::fs::metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
        if meta.permissions().mode() & 0o077 != 0 {
            return Err(format!(
                "{}: season secret file must not be group/other accessible (chmod 600)",
                path.display()
            ));
        }
        let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        // The error never echoes the file content.
        let key = hex_decode(text.trim())
            .map_err(|_| format!("{}: season secret must be hex", path.display()))?;
        let s = Self::from_bytes(key)?;
        if let Some(want) = expected_commit {
            if want.trim() != s.commitment {
                return Err(format!(
                    "{}: season secret commitment {} != published commitment {}",
                    path.display(),
                    s.commitment,
                    want.trim()
                ));
            }
        }
        Ok(s)
    }

    /// `sha256("near-arena-secret-commit-v1\0" || secret)`, published before
    /// the season opens and checked against the reveal at season end.
    pub fn commitment(&self) -> &str {
        &self.commitment
    }
}

/// Seeds for judge sampling of one job: bound to the challenge and the frozen
/// package digest, keyed by the season secret when the worker has one.
#[derive(Clone, Debug)]
pub struct SeedCtx {
    secret: Option<Arc<SeasonSecret>>,
    challenge_id: String,
    package_digest: String,
    tags: Vec<String>,
}

impl SeedCtx {
    pub fn new(
        secret: Option<Arc<SeasonSecret>>,
        challenge_id: &str,
        package_digest: &str,
    ) -> Self {
        SeedCtx {
            secret,
            challenge_id: challenge_id.into(),
            package_digest: package_digest.into(),
            tags: vec![],
        }
    }

    /// Public (secret-less) seeds.
    pub fn public(challenge_id: &str, package_digest: &str) -> Self {
        Self::new(None, challenge_id, package_digest)
    }

    /// A re-run that needs different inputs (`<class>#fresh`, ...).
    pub fn tagged(&self, tag: &str) -> Self {
        let mut s = self.clone();
        s.tags.push(tag.into());
        s
    }

    /// The generator seed of workload class `class_id`.
    ///
    /// Secret mode (BENCHMARK_SPEC §11.1): HMAC-SHA256 keyed by the season
    /// secret over `near-arena-workload-sample-v1|<challenge>|<package>|<c>`,
    /// where `<c>` is `class_id`, replaced by a tag that already starts with
    /// `<class_id>#` (`batch-1#fresh`) or else extended by `#<tag>`. Public
    /// mode: `derive_seed("workload", [class_id, challenge, package, tags..])`.
    pub fn class_seed(&self, class_id: &str) -> Result<u64, OracleError> {
        match &self.secret {
            None => {
                let mut parts = vec![class_id, &self.challenge_id, &self.package_digest];
                parts.extend(self.tags.iter().map(|t| t.as_str()));
                derive_seed("workload", &parts).map_err(OracleError::Broken)
            }
            Some(s) => {
                let mut c = class_id.to_string();
                for t in &self.tags {
                    if t.starts_with(&format!("{class_id}#")) {
                        c = t.clone();
                    } else {
                        c = format!("{c}#{t}");
                    }
                }
                for p in [&self.challenge_id, &self.package_digest, &c] {
                    if !seed_part_ok(p) {
                        return Err(OracleError::Broken(format!("bad seed part {p:?}")));
                    }
                }
                let msg = format!(
                    "{SAMPLING_DOMAIN}|{}|{}|{c}",
                    self.challenge_id, self.package_digest
                );
                let mac = hmac_sha256(&s.key, msg.as_bytes());
                Ok(u64::from_be_bytes(mac[..8].try_into().expect("8 bytes")))
            }
        }
    }

    /// Public description of the sampling mode (never the secret).
    pub fn mode(&self) -> String {
        match &self.secret {
            Some(s) => format!(
                "judge-secret HMAC sampling (season secret commitment {})",
                s.commitment()
            ),
            None => "PUBLIC sampling seeds (no season secret configured on this worker; inputs are predictable from the challenge id and package digest)".into(),
        }
    }
}

/// Minimum judge-sampled cases per workload class in any conformance suite.
pub const MIN_CASES_PER_CLASS: usize = 1;

fn is_unset(d: &Digest) -> bool {
    d.hex().bytes().all(|b| b == b'0')
}

/// What [`Oracles::conformance_suite`] assembled (counts are public; held-out
/// case ids are not).
#[derive(Debug)]
pub struct Suite {
    pub cases: Vec<Case>,
    pub public: usize,
    pub sampled: usize,
    pub heldout: usize,
    /// Public notes for the gate summary (sampling mode, held-out status).
    pub notes: Vec<String>,
}

/// Expected-reject cases (`Case::expected_claim` is empty and unused).
#[derive(Debug, Default)]
pub struct RejectionSet {
    pub cases: Vec<Case>,
    pub public: usize,
    pub sampled: usize,
    pub heldout: usize,
}

/// Oracle registry + fixture / held-out index + season secret.
#[derive(Default)]
pub struct Oracles {
    oracles: Vec<Box<dyn Oracle>>,
    fixtures: HashMap<Digest, PathBuf>,
    heldout: HashMap<Digest, PathBuf>,
    heldout_configured: bool,
    secret: Option<Arc<SeasonSecret>>,
}

impl Oracles {
    /// Built-in oracles (currently `demo-toy-arith-v1`).
    pub fn builtin() -> Self {
        Oracles {
            oracles: vec![Box::new(ToyArith)],
            ..Default::default()
        }
    }

    /// Built-ins plus the NEAR oracles (`near-arena-claim-v1` and
    /// `near-arena-claim-v2`) over the generator specs in `generators_dir`.
    pub fn with_near(self, oracle_bin: PathBuf, generators_dir: &Path) -> Result<Self, String> {
        self.with_near_dirs(oracle_bin, &[generators_dir.to_path_buf()])
    }

    /// As [`with_near`](Self::with_near) with several generator-spec dirs
    /// (e.g. the v1 and v2 workload suites). Specs are found by the digest the
    /// challenge commits to; each oracle only accepts specs of its scope.
    pub fn with_near_dirs(mut self, oracle_bin: PathBuf, dirs: &[PathBuf]) -> Result<Self, String> {
        let gens = Arc::new(NearOracle::index_generators(dirs)?);
        for scope in [NearScope::V1, NearScope::V2] {
            self.oracles.push(Box::new(NearOracle {
                scope,
                bin: oracle_bin.clone(),
                generators: gens.clone(),
            }));
        }
        Ok(self)
    }

    /// Register the v3 oracle (`near-arena-claim-v3`, binary
    /// `near-arena-oracle-v3`) over the generator specs in `dirs` (only specs
    /// whose `tool` is `near-arena-oracle-v3 gen` are used by it).
    pub fn with_near_v3(mut self, oracle_bin: PathBuf, dirs: &[PathBuf]) -> Result<Self, String> {
        self.oracles.push(Box::new(NearV3Oracle::new(oracle_bin, dirs)?));
        Ok(self)
    }

    pub fn register(&mut self, o: Box<dyn Oracle>) {
        self.oracles.push(o);
    }

    /// Key judge sampling with the season secret.
    pub fn set_season_secret(&mut self, s: SeasonSecret) {
        self.secret = Some(Arc::new(s));
    }

    /// Seeds for a job on (`challenge_id`, `package_digest`).
    pub fn seeds(&self, challenge_id: &str, package_digest: &str) -> SeedCtx {
        SeedCtx::new(self.secret.clone(), challenge_id, package_digest)
    }

    /// Index a fixtures directory by its TreeDigest.
    pub fn add_fixtures_dir(&mut self, dir: &Path) -> Result<Digest, String> {
        let d = tree_digest(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        self.fixtures.insert(d.clone(), dir.to_path_buf());
        Ok(d)
    }

    /// Index a judge-only held-out directory by its TreeDigest. Once any is
    /// configured, committed held-out sets are mandatory on this worker.
    pub fn add_heldout_dir(&mut self, dir: &Path) -> Result<Digest, String> {
        let d = tree_digest(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        self.heldout.insert(d.clone(), dir.to_path_buf());
        self.heldout_configured = true;
        Ok(d)
    }

    /// Require committed held-out sets even with no held-out dir indexed.
    pub fn require_heldout(&mut self) {
        self.heldout_configured = true;
    }

    /// Fixtures for a challenge, re-verified against the committed digest.
    /// `Ok(None)` only when the challenge pins no fixture set (all-zero
    /// digest); a pinned set this worker cannot supply is `Broken` (A06).
    pub fn fixtures_for(&self, chal: &ChallengeDefinition) -> Result<Option<PathBuf>, OracleError> {
        let want = &chal.workload_suite.public_fixtures;
        if is_unset(want) {
            return Ok(None);
        }
        let Some(dir) = self.fixtures.get(want) else {
            return Err(OracleError::Broken(format!(
                "fail-closed: the challenge pins public fixtures {want} (workload_suite.public_fixtures) \
                 but no ARENA_FIXTURES_DIRS entry on this worker has that TreeDigest"
            )));
        };
        reverify(dir, want, "fixtures")?;
        Ok(Some(dir.clone()))
    }

    /// The committed held-out set, re-verified against
    /// `workload_suite.heldout_commitment`. `Ok(None)` when nothing is
    /// committed or this worker has no held-out dirs configured.
    pub fn heldout_for(&self, chal: &ChallengeDefinition) -> Result<Option<PathBuf>, OracleError> {
        let want = &chal.workload_suite.heldout_commitment;
        if is_unset(want) || !self.heldout_configured {
            return Ok(None);
        }
        let Some(dir) = self.heldout.get(want) else {
            return Err(OracleError::Broken(format!(
                "fail-closed: the challenge commits to held-out set {want} \
                 (workload_suite.heldout_commitment) but no held-out dir on this worker has that TreeDigest"
            )));
        };
        reverify(dir, want, "held-out")?;
        Ok(Some(dir.clone()))
    }

    pub fn get(&self, chal: &ChallengeDefinition) -> Result<&dyn Oracle, OracleError> {
        let f = &chal.claim_encoding.format;
        self.oracles
            .iter()
            .find(|o| o.format() == f)
            .map(|b| b.as_ref())
            .ok_or_else(|| {
                OracleError::Unavailable(format!(
                    "no oracle for claim encoding {f:?} on this worker"
                ))
            })
    }

    /// The rejection cases of a challenge (public fixtures' `rejections/`,
    /// `n` judge-sampled, and `n` from the committed held-out set when this
    /// worker holds it), every request pin-checked by the caller. Encodings
    /// without rejection oracles yield an empty set.
    pub fn rejection_suite(
        &self,
        chal: &ChallengeDefinition,
        seeds: &SeedCtx,
        n: usize,
    ) -> Result<RejectionSet, OracleError> {
        let o = self.get(chal)?;
        let fixtures = self.fixtures_for(chal)?;
        let heldout = self.heldout_for(chal)?;
        o.rejection_cases(chal, fixtures.as_deref(), heldout.as_deref(), seeds, n)
    }

    /// The conformance suite: the pinned public fixtures, at least
    /// `max(MIN_CASES_PER_CLASS, ceil(samples / classes))` judge-sampled cases
    /// per workload class and, with `with_heldout`, as many committed
    /// held-out cases per class (seed-selected). Fails closed on a missing
    /// pinned set, a held-out digest mismatch or short coverage.
    pub fn conformance_suite(
        &self,
        chal: &ChallengeDefinition,
        seeds: &SeedCtx,
        samples: usize,
        with_heldout: bool,
    ) -> Result<Suite, OracleError> {
        let o = self.get(chal)?;
        let classes = &chal.workload_suite.classes;
        if classes.is_empty() {
            return Err(OracleError::Coverage(
                "the challenge's workload suite has no classes".into(),
            ));
        }
        let per_class = samples.div_ceil(classes.len()).max(MIN_CASES_PER_CLASS);
        let mut cases = vec![];
        let mut notes = vec![seeds.mode()];
        if let Some(dir) = self.fixtures_for(chal)? {
            let fx = o.fixture_cases(chal, &dir)?;
            if fx.is_empty() {
                return Err(OracleError::Coverage(format!(
                    "pinned public fixtures {} contain no in-domain case",
                    chal.workload_suite.public_fixtures
                )));
            }
            cases.extend(fx);
        }
        let public = cases.len();
        for c in classes {
            let got = o.sample(chal, &c.id, seeds, per_class)?;
            let n = got
                .iter()
                .filter(|x| x.class.as_deref() == Some(c.id.as_str()))
                .count();
            if n < per_class {
                return Err(OracleError::Coverage(format!(
                    "class {:?}: {n} judge-sampled case(s), at least {per_class} required",
                    c.id
                )));
            }
            cases.extend(got);
        }
        let sampled = cases.len() - public;
        let mut heldout = 0;
        let commit = &chal.workload_suite.heldout_commitment;
        if !with_heldout {
        } else if is_unset(commit) {
            notes.push("no held-out set committed".into());
        } else if let Some(dir) = self.heldout_for(chal)? {
            for c in classes {
                let mut h = o.heldout_cases(chal, &dir, &c.id)?;
                if h.is_empty() {
                    return Err(OracleError::Coverage(format!(
                        "committed held-out set {commit} has no in-domain case for class {:?}",
                        c.id
                    )));
                }
                let mut rng = SplitMix64::new(seeds.tagged("heldout").class_seed(&c.id)?);
                arena_measure::stats::shuffle(&mut h, &mut rng);
                h.truncate(per_class);
                for x in &mut h {
                    x.public = false;
                    x.class = Some(c.id.clone());
                }
                heldout += h.len();
                cases.extend(h);
            }
            notes.push(format!(
                "held-out set {commit} verified against the commitment and used ({heldout} case(s); ids withheld)"
            ));
        } else {
            notes.push(format!(
                "held-out set {commit} NOT exercised: no held-out dirs configured on this worker (ARENA_HELDOUT_DIRS)"
            ));
        }
        Ok(Suite {
            cases,
            public,
            sampled,
            heldout,
            notes,
        })
    }
}

fn tree_digest(dir: &Path) -> Result<Digest, String> {
    arena_archive::tree_from_dir(dir, &arena_archive::Limits::default())
        .map(|t| t.digest())
        .map_err(|e| e.to_string())
}

fn reverify(dir: &Path, want: &Digest, what: &str) -> Result<(), OracleError> {
    let got = tree_digest(dir).map_err(|e| OracleError::Broken(format!("{what} dir: {e}")))?;
    if &got != want {
        return Err(OracleError::Broken(format!(
            "fail-closed: {what} dir {} has TreeDigest {got}, the challenge commits to {want}",
            dir.display()
        )));
    }
    Ok(())
}

fn hex_encode(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn hex_decode(s: &str) -> Result<Vec<u8>, String> {
    if !s.len().is_multiple_of(2) || !s.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!("bad hex {s:?}"));
    }
    Ok((0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect())
}

/// `demo-toy-arith-v1` (challenges/demo/toy-arithmetic/SPEC.md):
/// request `a‖b`, empty witness, claim `a‖b‖(a·b mod 2^64)`, u64 LE.
/// Fixtures: `<name>.json` with `request_hex` (and optionally
/// `expected_claim_hex`, which must agree with the judge); a held-out set uses
/// the same files under `<class>/`.
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

    fn case(id: String, a: u64, b: u64, class: &str) -> Case {
        let mut request = a.to_le_bytes().to_vec();
        request.extend_from_slice(&b.to_le_bytes());
        let expected_claim = Self::expected_claim(&request).expect("16 bytes");
        Case {
            id,
            request,
            witness: vec![],
            expected_claim,
            public: false,
            class: Some(class.into()),
        }
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

    fn read_json_cases(dir: &Path, prefix: &str, public: bool) -> Result<Vec<Case>, OracleError> {
        let mut names: Vec<_> = std::fs::read_dir(dir)
            .map_err(|e| OracleError::Broken(format!("{}: {e}", dir.display())))?
            .filter_map(|e| e.ok()?.file_name().into_string().ok())
            .filter(|n| n.ends_with(".json"))
            .collect();
        names.sort();
        let mut out = vec![];
        for n in names {
            let v: serde_json::Value = serde_json::from_slice(
                &std::fs::read(dir.join(&n)).map_err(|e| OracleError::Broken(e.to_string()))?,
            )
            .map_err(|e| OracleError::Broken(format!("{prefix}{n}: {e}")))?;
            let req =
                hex_decode(v["request_hex"].as_str().unwrap_or("")).map_err(OracleError::Broken)?;
            let want = Self::expected_claim(&req)
                .ok_or_else(|| OracleError::Broken(format!("{prefix}{n}: bad request length")))?;
            // The judge computes the claim itself; the fixture's copy must agree.
            if let Some(h) = v["expected_claim_hex"].as_str() {
                if hex_decode(h).map_err(OracleError::Broken)? != want {
                    return Err(OracleError::Broken(format!(
                        "{prefix}{n}: fixture claim disagrees with the judge's oracle"
                    )));
                }
            }
            out.push(Case {
                id: format!("{prefix}{}", n.trim_end_matches(".json")),
                request: req,
                witness: vec![],
                expected_claim: want,
                public,
                class: None,
            });
        }
        Ok(out)
    }
}

impl Oracle for ToyArith {
    fn format(&self) -> &str {
        "demo-toy-arith-v1"
    }

    fn fixture_cases(
        &self,
        _chal: &ChallengeDefinition,
        dir: &Path,
    ) -> Result<Vec<Case>, OracleError> {
        Self::read_json_cases(dir, "fixture/", true)
    }

    fn heldout_cases(
        &self,
        _chal: &ChallengeDefinition,
        dir: &Path,
        class_id: &str,
    ) -> Result<Vec<Case>, OracleError> {
        let d = dir.join(class_id);
        if !d.is_dir() {
            return Ok(vec![]);
        }
        Self::read_json_cases(&d, &format!("heldout/{class_id}/"), false)
    }

    fn sample(
        &self,
        chal: &ChallengeDefinition,
        class_id: &str,
        seeds: &SeedCtx,
        n: usize,
    ) -> Result<Vec<Case>, OracleError> {
        let bits = Self::bits(chal, class_id)?;
        let mut rng = SplitMix64::new(seeds.class_seed(class_id)?);
        let mask = if bits >= 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };
        Ok((0..n)
            .map(|i| {
                let a = rng.next_u64() & mask;
                let b = rng.next_u64() & mask;
                Self::case(format!("{class_id}/{i}"), a, b, class_id)
            })
            .collect())
    }
}

/// The two NEAR claim encodings ([`NearOracle`] is registered once for each).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NearScope {
    /// `near-arena-claim-v1` (spec/claim-v1.md), oracle `--scope v1`.
    V1,
    /// `near-arena-claim-v2` (spec/claim-v2.md), oracle `--scope v2`.
    V2,
}

impl NearScope {
    pub fn format(self) -> &'static str {
        match self {
            NearScope::V1 => "near-arena-claim-v1",
            NearScope::V2 => "near-arena-claim-v2",
        }
    }
    fn flag(self) -> &'static str {
        match self {
            NearScope::V1 => "v1",
            NearScope::V2 => "v2",
        }
    }
}

/// `near-arena-claim-v1` / `near-arena-claim-v2` (spec/near-transfer-receipt-
/// {v1,v2}.md): requests, witnesses and expected claims are produced by the
/// governed oracle (`near-arena-oracle`, which executes the pinned nearcore
/// runtime). Public fixtures come from the digest-matched fixtures dir
/// (`cases/<name>/{request,witness,expected_claim}.bin`, `params.bin`);
/// sampled batches run `near-arena-oracle gen` with the arguments of the
/// class's generator spec (located by the digest the challenge commits to,
/// and required to name this oracle's `--scope`) and a judge-derived seed.
/// Held-out sets: `<class>/{params.bin, cases/<name>/...}`.
pub struct NearOracle {
    scope: NearScope,
    bin: PathBuf,
    generators: Arc<HashMap<Digest, serde_json::Value>>,
}

static GEN_RUN: AtomicU64 = AtomicU64::new(0);

impl NearOracle {
    pub fn new(
        scope: NearScope,
        bin: PathBuf,
        generators_dirs: &[PathBuf],
    ) -> Result<Self, String> {
        Ok(NearOracle {
            scope,
            bin,
            generators: Arc::new(Self::index_generators(generators_dirs)?),
        })
    }

    fn index_generators(dirs: &[PathBuf]) -> Result<HashMap<Digest, serde_json::Value>, String> {
        let mut generators = HashMap::new();
        for dir in dirs {
            for e in std::fs::read_dir(dir)
                .map_err(|e| format!("{}: {e}", dir.display()))?
                .flatten()
            {
                let p = e.path();
                if p.extension().is_some_and(|x| x == "json") {
                    let v: serde_json::Value =
                        serde_json::from_slice(&std::fs::read(&p).map_err(|e| e.to_string())?)
                            .map_err(|e| format!("{}: {e}", p.display()))?;
                    let d = arena_types::sha256_digest(&v).map_err(|e| e.to_string())?;
                    generators.insert(d, v);
                }
            }
        }
        Ok(generators)
    }

    /// The generator args, checked to be for this oracle's scope.
    fn generator_args(&self, spec: &serde_json::Value) -> Result<Vec<String>, OracleError> {
        let args: Vec<String> = spec["args"]
            .as_array()
            .map(|a| {
                a.iter()
                    .filter_map(|x| x.as_str().map(String::from))
                    .collect()
            })
            .unwrap_or_default();
        if !args.iter().any(|a| a == "--fixtures-layout") {
            return Err(OracleError::Broken(
                "generator spec must use --fixtures-layout".into(),
            ));
        }
        let scope = args
            .iter()
            .position(|a| a == "--scope")
            .map(|i| args.get(i + 1).map(String::as_str).unwrap_or(""))
            .unwrap_or("v1");
        if scope != self.scope.flag() {
            return Err(OracleError::Broken(format!(
                "fail-closed: generator spec is for --scope {scope}, the challenge's claim encoding {} needs --scope {}",
                self.scope.format(),
                self.scope.flag()
            )));
        }
        Ok(args)
    }

    fn read_cases(
        dir: &Path,
        public: bool,
        prefix: &str,
        class: Option<&str>,
    ) -> Result<Vec<Case>, OracleError> {
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
            let Ok(expected_claim) = std::fs::read(d.join("expected_claim.bin")) else {
                continue;
            };
            let rd = |f: &str| {
                std::fs::read(d.join(f)).map_err(|e| {
                    OracleError::Broken(if public {
                        format!("{n}/{f}: {e}")
                    } else {
                        format!("{prefix}*/{f}: {}", e.kind())
                    })
                })
            };
            out.push(Case {
                id: format!("{prefix}{n}"),
                request: rd("request.bin")?,
                witness: rd("witness.bin")?,
                expected_claim,
                public,
                class: class.map(String::from),
            });
        }
        Ok(out)
    }
}

impl Oracle for NearOracle {
    fn format(&self) -> &str {
        self.scope.format()
    }

    fn fixture_cases(
        &self,
        _chal: &ChallengeDefinition,
        dir: &Path,
    ) -> Result<Vec<Case>, OracleError> {
        Self::read_cases(&dir.join("cases"), true, "fixture/", None)
    }

    fn heldout_cases(
        &self,
        chal: &ChallengeDefinition,
        dir: &Path,
        class_id: &str,
    ) -> Result<Vec<Case>, OracleError> {
        let d = dir.join(class_id);
        if !d.is_dir() {
            return Ok(vec![]);
        }
        // The held-out set must be for the same statement / parameters.
        if let Ok(p) = std::fs::read(d.join("params.bin")) {
            if let Some(pin) = crate::jobs::RequestPin::from_challenge(chal) {
                pin.check_params(&p, &chal.runtime_config_digest)
                    .map_err(|e| OracleError::Broken(format!("held-out params.bin: {e}")))?;
            }
        }
        Self::read_cases(
            &d.join("cases"),
            false,
            &format!("heldout/{class_id}/"),
            Some(class_id),
        )
    }

    fn sample(
        &self,
        chal: &ChallengeDefinition,
        class_id: &str,
        seeds: &SeedCtx,
        n: usize,
    ) -> Result<Vec<Case>, OracleError> {
        if n == 0 {
            return Ok(vec![]);
        }
        let class = chal
            .workload_suite
            .classes
            .iter()
            .find(|c| c.id == class_id)
            .ok_or_else(|| OracleError::Broken(format!("unknown class {class_id:?}")))?;
        let spec = self.generators.get(&class.generator).ok_or_else(|| {
            OracleError::Unavailable(format!(
                "no generator spec with digest {} on this worker",
                class.generator
            ))
        })?;
        let args = self.generator_args(spec)?;
        let seed = seeds.class_seed(class_id)?;
        // The seed may be secret-derived: it is not put in paths or messages.
        let out_dir = std::env::temp_dir().join(format!(
            "near-oracle-{}-{}",
            std::process::id(),
            GEN_RUN.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&out_dir);
        let o = std::process::Command::new(&self.bin)
            .arg("gen")
            .args([
                "--seed",
                &seed.to_string(),
                "--valid",
                &n.to_string(),
                "--invalid",
                "0",
                "--out",
            ])
            .arg(&out_dir)
            .args(&args)
            .output()
            .map_err(|e| OracleError::Broken(format!("near-arena-oracle: {e}")))?;
        if !o.status.success() {
            let _ = std::fs::remove_dir_all(&out_dir);
            return Err(OracleError::Broken(format!(
                "near-arena-oracle gen failed: {}",
                String::from_utf8_lossy(&o.stderr)
            )));
        }
        let cases = Self::read_cases(
            &out_dir.join("cases"),
            false,
            &format!("{class_id}/"),
            Some(class_id),
        );
        let _ = std::fs::remove_dir_all(&out_dir);
        let cases = cases?;
        if cases.is_empty() {
            return Err(OracleError::Broken(format!(
                "generator produced no in-domain cases for {class_id}"
            )));
        }
        Ok(cases)
    }

    fn approved_params(
        &self,
        chal: &ChallengeDefinition,
        fixtures: Option<&Path>,
    ) -> Result<Vec<u8>, OracleError> {
        let f = fixtures.ok_or_else(|| {
            OracleError::Unavailable(format!(
                "{} needs the public fixtures (params.bin)",
                self.format()
            ))
        })?;
        let p = std::fs::read(f.join("params.bin"))
            .map_err(|e| OracleError::Broken(format!("params.bin: {e}")))?;
        if let Some(pin) = crate::jobs::RequestPin::from_challenge(chal) {
            pin.check_params(&p, &chal.runtime_config_digest)
                .map_err(|e| OracleError::Broken(format!("fail-closed: params.bin: {e}")))?;
        }
        Ok(p)
    }
}


/// Read `<dir>/<name>/{request,witness,expected_claim}.bin` case dirs, sorted
/// by name. `rejections = false`: dirs without `expected_claim.bin` are
/// skipped (never issued as positives); `true`: every dir is read as an
/// expected-reject case (`expected_claim` empty). Non-public read errors never
/// name the case.
fn read_case_dirs(
    dir: &Path,
    public: bool,
    prefix: &str,
    class: Option<&str>,
    rejections: bool,
) -> Result<Vec<Case>, OracleError> {
    let mut names: Vec<String> = match std::fs::read_dir(dir) {
        Ok(rd) => rd
            .flatten()
            .filter(|e| e.path().is_dir())
            .filter_map(|e| e.file_name().into_string().ok())
            .collect(),
        Err(e) if rejections && e.kind() == std::io::ErrorKind::NotFound => return Ok(vec![]),
        Err(e) => return Err(OracleError::Broken(format!("{}: {e}", dir.display()))),
    };
    names.sort();
    let mut out = vec![];
    for n in names {
        let d = dir.join(&n);
        let rd = |f: &str| {
            std::fs::read(d.join(f)).map_err(|e| {
                OracleError::Broken(if public {
                    format!("{n}/{f}: {e}")
                } else {
                    format!("{prefix}*/{f}: {}", e.kind())
                })
            })
        };
        let expected_claim = if rejections {
            vec![]
        } else {
            match std::fs::read(d.join("expected_claim.bin")) {
                Ok(c) => c,
                Err(_) => continue,
            }
        };
        out.push(Case {
            id: format!("{prefix}{n}"),
            request: rd("request.bin")?,
            witness: rd("witness.bin")?,
            expected_claim,
            public,
            class: class.map(String::from),
        });
    }
    Ok(out)
}

/// `near-arena-claim-v3` (spec/near-chunk-validation-v0.md, spec/claim-v3.md):
/// the judge-owned oracle `near-arena-oracle-v3` drives real multi-shard
/// nearcore `TestEnv` chains, captures the `ChunkStateWitness` bytes chunk
/// producers emit, builds the claim from the producing node's store and epoch
/// manager, and labels every case with **nearcore's own validator verdict**
/// (`pre_validate_chunk_state_witness` + `validate_chunk_state_witness`) and
/// an independent D0 classifier.
///
/// Arena layout (`gen --fixtures-layout`): `cases/<n>/{request.bin,
/// witness.bin, expected_claim.bin}` with `request = expected_claim =
/// claim.bin` for `Rel_D0` cases (nearcore accepts and the chunk is in D0),
/// `rejections/<n>/{request.bin, witness.bin}` for the others (nearcore
/// rejects, or the honest chunk is outside D0), and `params.bin`
/// (`near-arena-params-v3`). Held-out sets: `<class>/{params.bin, cases/}`
/// plus `rejections/`.
///
/// Sampling runs `near-arena-oracle-v3 gen --fixtures-layout --d0-target n`
/// with the class's generator-spec args (located by the digest the challenge
/// commits to; the spec must name this tool and this class) and a
/// judge-derived seed; rejection sampling runs the judge's fixed
/// [`NearV3Oracle::REJECTION_ARGS`] with the seed of pseudo-class
/// `rejections`.
pub struct NearV3Oracle {
    bin: PathBuf,
    generators: Arc<HashMap<Digest, serde_json::Value>>,
}

impl NearV3Oracle {
    pub const FORMAT: &'static str = "near-arena-claim-v3";
    pub const TOOL: &'static str = "near-arena-oracle-v3 gen";
    /// Judge-fixed rejection sampling: one honest 40-block chain (parameter
    /// set rotated by the seed: 4/5/6 shards, Reed-Solomon (2,8), (33,100),
    /// (5,16), (1,3)), every third honest D0 chunk mutated (nearcore judges
    /// each mutant), out-of-domain honest chunks capped at 3 per violation
    /// family, no positives. The judge then picks `n` of the written
    /// rejections, alternating out-of-domain chunks and mutants, by a
    /// seed-keyed shuffle.
    pub const REJECTION_ARGS: &'static [&'static str] = &[
        "--fixtures-layout",
        "--no-positives",
        "--rotate",
        "--mutate-every",
        "3",
        "--ood-cap",
        "3",
        "--chains",
        "1",
        "--blocks",
        "40",
    ];

    pub fn new(bin: PathBuf, generators_dirs: &[PathBuf]) -> Result<Self, String> {
        Ok(NearV3Oracle {
            bin,
            generators: Arc::new(NearOracle::index_generators(generators_dirs)?),
        })
    }

    /// The class's generator args: the spec must be for this tool and class,
    /// and may not set the judge-controlled output options.
    fn generator_args(&self, spec: &serde_json::Value, class_id: &str) -> Result<Vec<String>, OracleError> {
        if spec["tool"].as_str() != Some(Self::TOOL) {
            return Err(OracleError::Broken(format!(
                "fail-closed: generator spec tool {:?} is not {:?} (claim encoding {})",
                spec["tool"].as_str().unwrap_or(""),
                Self::TOOL,
                Self::FORMAT
            )));
        }
        if spec["class"].as_str() != Some(class_id) {
            return Err(OracleError::Broken(format!(
                "fail-closed: generator spec is for class {:?}, not {class_id:?}",
                spec["class"].as_str().unwrap_or("")
            )));
        }
        let args: Vec<String> = spec["args"]
            .as_array()
            .map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect())
            .unwrap_or_default();
        for judge_owned in ["--seed", "--out", "--d0-target", "--rejection-target", "--no-positives", "--accepted-mutants"] {
            if args.iter().any(|a| a == judge_owned) {
                return Err(OracleError::Broken(format!(
                    "fail-closed: generator spec sets the judge-owned option {judge_owned}"
                )));
            }
        }
        if !args.iter().any(|a| a == "--fixtures-layout") || !args.iter().any(|a| a == "--class") {
            return Err(OracleError::Broken(
                "generator spec must use --fixtures-layout and name a --class".into(),
            ));
        }
        Ok(args)
    }

    /// Run the oracle into a fresh temp dir; `read` gets the dir.
    fn gen<T>(
        &self,
        seed: u64,
        args: &[String],
        read: impl FnOnce(&Path) -> Result<T, OracleError>,
    ) -> Result<T, OracleError> {
        // The seed may be secret-derived: it is not put in paths or messages.
        let out_dir = std::env::temp_dir().join(format!(
            "near-oracle-v3-{}-{}",
            std::process::id(),
            GEN_RUN.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = std::fs::remove_dir_all(&out_dir);
        let o = std::process::Command::new(&self.bin)
            .arg("gen")
            .args(["--seed", &seed.to_string(), "--out"])
            .arg(&out_dir)
            .args(args)
            .output()
            .map_err(|e| OracleError::Broken(format!("near-arena-oracle-v3: {e}")));
        let res = o.and_then(|o| {
            if o.status.success() {
                read(&out_dir)
            } else {
                // stderr names chain parameters and case names, never the seed
                let tail: String = String::from_utf8_lossy(&o.stderr)
                    .lines()
                    .rev()
                    .take(4)
                    .collect::<Vec<_>>()
                    .join(" | ");
                Err(OracleError::Broken(format!(
                    "near-arena-oracle-v3 gen failed ({}): {tail}",
                    o.status
                )))
            }
        });
        let _ = std::fs::remove_dir_all(&out_dir);
        res
    }
}

impl Oracle for NearV3Oracle {
    fn format(&self) -> &str {
        Self::FORMAT
    }

    fn fixture_cases(
        &self,
        _chal: &ChallengeDefinition,
        dir: &Path,
    ) -> Result<Vec<Case>, OracleError> {
        read_case_dirs(&dir.join("cases"), true, "fixture/", None, false)
    }

    fn heldout_cases(
        &self,
        chal: &ChallengeDefinition,
        dir: &Path,
        class_id: &str,
    ) -> Result<Vec<Case>, OracleError> {
        let d = dir.join(class_id);
        if !d.is_dir() {
            return Ok(vec![]);
        }
        let p = std::fs::read(d.join("params.bin"))
            .map_err(|e| OracleError::Broken(format!("held-out params.bin: {}", e.kind())))?;
        if let Some(pin) = crate::jobs::RequestPin::from_challenge(chal) {
            pin.check_params(&p, &chal.runtime_config_digest)
                .map_err(|e| OracleError::Broken(format!("held-out params.bin: {e}")))?;
        }
        read_case_dirs(&d.join("cases"), false, &format!("heldout/{class_id}/"), Some(class_id), false)
    }

    fn sample(
        &self,
        chal: &ChallengeDefinition,
        class_id: &str,
        seeds: &SeedCtx,
        n: usize,
    ) -> Result<Vec<Case>, OracleError> {
        if n == 0 {
            return Ok(vec![]);
        }
        let class = chal
            .workload_suite
            .classes
            .iter()
            .find(|c| c.id == class_id)
            .ok_or_else(|| OracleError::Broken(format!("unknown class {class_id:?}")))?;
        let spec = self.generators.get(&class.generator).ok_or_else(|| {
            OracleError::Unavailable(format!(
                "no generator spec with digest {} on this worker",
                class.generator
            ))
        })?;
        let mut args = self.generator_args(spec, class_id)?;
        args.extend(["--d0-target".to_string(), n.to_string()]);
        let seed = seeds.class_seed(class_id)?;
        let cases = self.gen(seed, &args, |d| {
            read_case_dirs(&d.join("cases"), false, &format!("{class_id}/"), Some(class_id), false)
        })?;
        if cases.len() != n {
            return Err(OracleError::Broken(format!(
                "generator produced {} in-domain case(s) for {class_id}, {n} requested",
                cases.len()
            )));
        }
        Ok(cases)
    }

    fn rejection_cases(
        &self,
        _chal: &ChallengeDefinition,
        fixtures: Option<&Path>,
        heldout: Option<&Path>,
        seeds: &SeedCtx,
        n: usize,
    ) -> Result<RejectionSet, OracleError> {
        let mut set = RejectionSet::default();
        if let Some(f) = fixtures {
            let c = read_case_dirs(&f.join("rejections"), true, "fixture-reject/", None, true)?;
            set.public = c.len();
            set.cases.extend(c);
        }
        if n > 0 {
            let args: Vec<String> = Self::REJECTION_ARGS.iter().map(|s| s.to_string()).collect();
            let seed = seeds.class_seed("rejections")?;
            let (mut ood, mut mutants) = self.gen(seed, &args, |d| {
                let dir = d.join("rejections");
                let all = read_case_dirs(&dir, false, "rejections/", None, true)?;
                let mut ood = vec![];
                let mut mutants = vec![];
                for c in all {
                    let name = c.id.trim_start_matches("rejections/");
                    let meta = std::fs::read(dir.join(name).join("meta.json")).unwrap_or_default();
                    let kind = serde_json::from_slice::<serde_json::Value>(&meta)
                        .ok()
                        .and_then(|m| m["kind"].as_str().map(String::from));
                    match kind.as_deref() {
                        Some("mutant") => mutants.push(c),
                        Some("honest") => ood.push(c),
                        _ => return Err(OracleError::Broken("rejection case without a kind".into())),
                    }
                }
                Ok((ood, mutants))
            })?;
            let mut rng = SplitMix64::new(seed ^ 0x7265_6a65_6374_696f);
            arena_measure::stats::shuffle(&mut ood, &mut rng);
            arena_measure::stats::shuffle(&mut mutants, &mut rng);
            let (mut a, mut b) = (ood.into_iter(), mutants.into_iter());
            let mut picked = vec![];
            while picked.len() < n {
                let x = if picked.len() % 2 == 0 { a.next().or_else(|| b.next()) } else { b.next().or_else(|| a.next()) };
                match x {
                    Some(c) => picked.push(c),
                    None => break,
                }
            }
            if picked.len() < n {
                return Err(OracleError::Coverage(format!(
                    "{} judge-sampled rejection case(s), {n} required",
                    picked.len()
                )));
            }
            set.sampled = picked.len();
            set.cases.extend(picked);
        }
        if let Some(h) = heldout {
            let mut c = read_case_dirs(&h.join("rejections"), false, "heldout-reject/", None, true)?;
            if c.is_empty() {
                return Err(OracleError::Coverage(
                    "the committed held-out set has no rejection cases".into(),
                ));
            }
            let mut rng = SplitMix64::new(seeds.tagged("heldout").class_seed("rejections")?);
            arena_measure::stats::shuffle(&mut c, &mut rng);
            c.truncate(n.max(1));
            set.heldout = c.len();
            set.cases.extend(c);
        }
        Ok(set)
    }

    fn approved_params(
        &self,
        chal: &ChallengeDefinition,
        fixtures: Option<&Path>,
    ) -> Result<Vec<u8>, OracleError> {
        let f = fixtures.ok_or_else(|| {
            OracleError::Unavailable(format!("{} needs the public fixtures (params.bin)", Self::FORMAT))
        })?;
        let p = std::fs::read(f.join("params.bin"))
            .map_err(|e| OracleError::Broken(format!("params.bin: {e}")))?;
        let pin = crate::jobs::RequestPin::from_challenge(chal)
            .ok_or_else(|| OracleError::Broken("v3 challenge without a request pin".into()))?;
        pin.check_params(&p, &chal.runtime_config_digest)
            .map_err(|e| OracleError::Broken(format!("fail-closed: params.bin: {e}")))?;
        Ok(p)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn repo() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }
    fn load(rel: &str) -> ChallengeDefinition {
        serde_json::from_slice(&std::fs::read(repo().join(rel)).unwrap()).unwrap()
    }
    fn toy() -> ChallengeDefinition {
        load("challenges/chl_54c65fe7c73c5abcfe500681889177bc.json")
    }
    fn toy_fixtures() -> PathBuf {
        repo().join("challenges/demo/toy-arithmetic/fixtures")
    }
    fn seeds() -> SeedCtx {
        SeedCtx::public("chl_x", &format!("sha256:{}", "ab".repeat(32)))
    }
    fn zero() -> Digest {
        Digest::try_from(format!("sha256:{}", "0".repeat(64))).unwrap()
    }

    #[test]
    fn toy_claim() {
        let mut r = 3u64.to_le_bytes().to_vec();
        r.extend_from_slice(&u64::MAX.to_le_bytes());
        let c = ToyArith::expected_claim(&r).unwrap();
        assert_eq!(&c[16..], &3u64.wrapping_mul(u64::MAX).to_le_bytes());
        assert!(ToyArith::expected_claim(&r[..15]).is_none());
    }

    /// A06: a pinned public fixture set the worker cannot supply is an infra
    /// error naming the pin; it never degrades to generated-only cases.
    #[test]
    fn missing_pinned_fixtures_fail_closed() {
        let chal = toy();
        let o = Oracles::builtin();
        let e = o.conformance_suite(&chal, &seeds(), 4, true).unwrap_err();
        assert!(matches!(e, OracleError::Broken(_)), "{e}");
        assert!(
            e.to_string()
                .contains(chal.workload_suite.public_fixtures.as_str()),
            "{e}"
        );
        // With the pinned set present: fixtures + every class sampled.
        let mut o = Oracles::builtin();
        o.add_fixtures_dir(&toy_fixtures()).unwrap();
        let s = o.conformance_suite(&chal, &seeds(), 4, true).unwrap();
        assert_eq!(s.public, 6);
        assert_eq!(s.sampled, 4);
        // A fixtures dir that changes after indexing is caught on use.
        let tmp = tempfile::tempdir().unwrap();
        for e in std::fs::read_dir(toy_fixtures()).unwrap().flatten() {
            std::fs::copy(e.path(), tmp.path().join(e.file_name())).unwrap();
        }
        let mut o = Oracles::builtin();
        o.add_fixtures_dir(tmp.path()).unwrap();
        std::fs::write(tmp.path().join("extra.txt"), "x").unwrap();
        let e = o.conformance_suite(&chal, &seeds(), 4, true).unwrap_err();
        assert!(e.to_string().contains("TreeDigest"), "{e}");
        // Only an explicitly unpinned (all-zero) fixtures digest runs without.
        let mut unpinned = chal.clone();
        unpinned.workload_suite.public_fixtures = zero();
        let s = Oracles::builtin()
            .conformance_suite(&unpinned, &seeds(), 4, true)
            .unwrap();
        assert_eq!((s.public, s.sampled), (0, 4));
    }

    /// An oracle whose generator under-delivers for one class.
    struct Short;
    impl Oracle for Short {
        fn format(&self) -> &str {
            "test-short"
        }
        fn fixture_cases(
            &self,
            c: &ChallengeDefinition,
            d: &Path,
        ) -> Result<Vec<Case>, OracleError> {
            ToyArith.fixture_cases(c, d)
        }
        fn sample(
            &self,
            c: &ChallengeDefinition,
            class_id: &str,
            s: &SeedCtx,
            n: usize,
        ) -> Result<Vec<Case>, OracleError> {
            let n = if class_id == "toy-large" { n - 1 } else { n };
            ToyArith.sample(c, class_id, s, n)
        }
    }

    /// A06: every workload class must contribute its minimum sampled cases.
    #[test]
    fn insufficient_class_coverage_fails_closed() {
        let mut chal = toy();
        chal.claim_encoding.format = "test-short".into();
        let mut o = Oracles::default();
        o.register(Box::new(Short));
        o.add_fixtures_dir(&toy_fixtures()).unwrap();
        for samples in [0, 1, 4, 8] {
            let e = o
                .conformance_suite(&chal, &seeds(), samples, true)
                .unwrap_err();
            assert!(matches!(e, OracleError::Coverage(_)), "{e}");
            assert!(e.to_string().contains("toy-large"), "{e}");
        }
        // A fixture set with no in-domain case is not coverage either.
        let tmp = tempfile::tempdir().unwrap();
        std::fs::write(tmp.path().join("README"), "no cases").unwrap();
        let mut chal = toy();
        let mut o = Oracles::builtin();
        chal.workload_suite.public_fixtures = o.add_fixtures_dir(tmp.path()).unwrap();
        let e = o.conformance_suite(&chal, &seeds(), 4, true).unwrap_err();
        assert!(matches!(e, OracleError::Coverage(_)), "{e}");
        // The floor applies even with no configured samples.
        let s = Oracles::builtin()
            .conformance_suite(
                &{
                    let mut c = toy();
                    c.workload_suite.public_fixtures = zero();
                    c
                },
                &seeds(),
                0,
                false,
            )
            .unwrap();
        assert_eq!(
            s.sampled,
            chal.workload_suite.classes.len() * MIN_CASES_PER_CLASS
        );
    }

    fn toy_heldout(dir: &Path) {
        for (class, k) in [("toy-small", 3u64), ("toy-large", 5u64)] {
            std::fs::create_dir_all(dir.join(class)).unwrap();
            for i in 0..k {
                let mut r = (1000 + i).to_le_bytes().to_vec();
                r.extend_from_slice(&(77 * i + 1).to_le_bytes());
                let h: String = r.iter().map(|x| format!("{x:02x}")).collect();
                std::fs::write(
                    dir.join(class).join(format!("secret-{i}.json")),
                    format!("{{\"request_hex\":\"{h}\"}}"),
                )
                .unwrap();
            }
        }
    }

    /// A06: committed held-out sets are loaded from judge-only dirs,
    /// verified against the commitment, used, and never public.
    #[test]
    fn heldout_set_is_verified_against_the_commitment() {
        let tmp = tempfile::tempdir().unwrap();
        let hd = tmp.path().join("heldout");
        toy_heldout(&hd);
        let mut chal = toy();
        let mut o = Oracles::builtin();
        o.add_fixtures_dir(&toy_fixtures()).unwrap();
        // Not configured on this worker: reported, not silently passed over.
        chal.workload_suite.heldout_commitment = Digest::of_bytes(b"other");
        let s = o.conformance_suite(&chal, &seeds(), 4, true).unwrap();
        assert_eq!(s.heldout, 0);
        assert!(
            s.notes.iter().any(|n| n.contains("NOT exercised")),
            "{:?}",
            s.notes
        );
        // Configured, but the commitment names a different set: infra error.
        let d = o.add_heldout_dir(&hd).unwrap();
        let e = o.conformance_suite(&chal, &seeds(), 4, true).unwrap_err();
        assert!(matches!(e, OracleError::Broken(_)), "{e}");
        assert!(e.to_string().contains("heldout_commitment"), "{e}");
        // Matching commitment: used, never public, ids not in the notes.
        chal.workload_suite.heldout_commitment = d.clone();
        let s = o.conformance_suite(&chal, &seeds(), 4, true).unwrap();
        assert_eq!(s.heldout, 4);
        let h: Vec<_> = s
            .cases
            .iter()
            .filter(|c| c.id.starts_with("heldout/"))
            .collect();
        assert_eq!(h.len(), 4);
        assert!(h.iter().all(|c| !c.public && c.class.is_some()));
        assert!(
            s.notes.iter().all(|n| !n.contains("secret-")),
            "{:?}",
            s.notes
        );
        // Adversarial suites never carry held-out cases.
        let s = o.conformance_suite(&chal, &seeds(), 4, false).unwrap();
        assert_eq!(s.heldout, 0);
        // A held-out dir edited after indexing no longer matches.
        std::fs::write(
            hd.join("toy-small/secret-0.json"),
            "{\"request_hex\":\"00\"}",
        )
        .unwrap();
        let e = o.conformance_suite(&chal, &seeds(), 4, true).unwrap_err();
        assert!(e.to_string().contains("TreeDigest"), "{e}");
        // `require_heldout` without any dir: a committed set is mandatory.
        let mut o = Oracles::builtin();
        o.add_fixtures_dir(&toy_fixtures()).unwrap();
        o.require_heldout();
        assert!(o.conformance_suite(&chal, &seeds(), 4, true).is_err());
    }

    /// BENCHMARK_SPEC §11.1 vectors (benchmarks/arena_bench/seeds.py):
    /// with a season secret, seeds are unpredictable from public inputs and
    /// change with the secret.
    #[test]
    fn judge_secret_sampling_seeds() {
        let pkg = format!("sha256:{}", "ab".repeat(32));
        let s1 = Arc::new(SeasonSecret::from_bytes((0u8..32).collect()).unwrap());
        let s2 = Arc::new(SeasonSecret::from_bytes((1u8..33).collect()).unwrap());
        assert_eq!(
            s1.commitment(),
            "sha256:96c1f9dd885e964b0f9396d97985bfab97ed71aa58d646db045c0175e64f78e7"
        );
        let a = SeedCtx::new(Some(s1.clone()), "chl_x", &pkg);
        let b = SeedCtx::new(Some(s2), "chl_x", &pkg);
        let p = SeedCtx::public("chl_x", &pkg);
        assert_eq!(a.class_seed("batch-1").unwrap(), 18162950082924812480);
        assert_eq!(
            a.tagged("batch-1#fresh").class_seed("batch-1").unwrap(),
            5464440875880823750
        );
        assert_eq!(b.class_seed("batch-1").unwrap(), 13682769913092145860);
        assert_ne!(
            a.class_seed("batch-1").unwrap(),
            p.class_seed("batch-1").unwrap()
        );
        // Public mode is unchanged: derive_seed("workload", class, chal, pkg).
        assert_eq!(
            p.class_seed("batch-1").unwrap(),
            derive_seed("workload", &["batch-1", "chl_x", &pkg]).unwrap()
        );
        // Sampled inputs differ with the secret.
        let chal = toy();
        let ca = ToyArith
            .sample(
                &chal,
                "toy-large",
                &SeedCtx::new(Some(s1), "chl_x", &pkg),
                3,
            )
            .unwrap();
        let cp = ToyArith.sample(&chal, "toy-large", &p, 3).unwrap();
        assert_ne!(ca, cp);
        assert!(a.mode().contains(
            SeasonSecret::from_bytes((0u8..32).collect())
                .unwrap()
                .commitment()
        ));
        assert!(p.mode().contains("PUBLIC"));
        assert!(SeasonSecret::from_bytes(vec![1; 31]).is_err());
    }

    #[test]
    fn season_secret_file_is_judge_only_and_never_printed() {
        use std::os::unix::fs::PermissionsExt;
        let tmp = tempfile::tempdir().unwrap();
        let f = tmp.path().join("secret");
        let hex: String = (0u8..32).map(|x| format!("{x:02x}")).collect();
        std::fs::write(&f, format!("{hex}\n")).unwrap();
        std::fs::set_permissions(&f, std::fs::Permissions::from_mode(0o644)).unwrap();
        let e = SeasonSecret::from_file(&f, None).unwrap_err();
        assert!(e.contains("chmod 600") && !e.contains(&hex), "{e}");
        std::fs::set_permissions(&f, std::fs::Permissions::from_mode(0o600)).unwrap();
        let s = SeasonSecret::from_file(&f, None).unwrap();
        let commit = s.commitment().to_string();
        assert!(!format!("{s:?}").contains(&hex[..16]));
        assert!(!SeedCtx::new(Some(Arc::new(s)), "c", "p")
            .mode()
            .contains(&hex[..16]));
        assert!(SeasonSecret::from_file(&f, Some(&commit)).is_ok());
        let e =
            SeasonSecret::from_file(&f, Some(&format!("sha256:{}", "1".repeat(64)))).unwrap_err();
        assert!(
            e.contains("published commitment") && !e.contains(&hex),
            "{e}"
        );
        std::fs::write(&f, "not hex at all, but secret-ish").unwrap();
        let e = SeasonSecret::from_file(&f, None).unwrap_err();
        assert!(!e.contains("secret-ish"), "{e}");
    }

    /// A04: v1 and v2 are separate registrations; a generator spec of the
    /// other scope is refused; unknown encodings stay UNKNOWN.
    #[test]
    fn near_v1_and_v2_oracles_are_distinct() {
        let gens = [
            repo().join("spec/workloads/near-transfer-receipt-v1"),
            repo().join("spec/workloads/near-transfer-receipt-v2"),
        ];
        let o = Oracles::builtin()
            .with_near_dirs(PathBuf::from("/nonexistent/near-arena-oracle"), &gens)
            .unwrap();
        let v1 = load("challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json");
        let v2 = load("challenges/drafts/near-transfer-receipt-v2.draft.json");
        assert_eq!(o.get(&v1).unwrap().format(), "near-arena-claim-v1");
        assert_eq!(o.get(&v2).unwrap().format(), "near-arena-claim-v2");
        let mut v3 = v2.clone();
        v3.claim_encoding.format = "near-arena-claim-v3".into();
        assert!(matches!(o.get(&v3), Err(OracleError::Unavailable(_))));
        // v1 challenge whose class points at a v2 generator spec (and vice
        // versa): refused before the oracle binary runs.
        let mut x = v1.clone();
        x.workload_suite.classes[0].generator = v2.workload_suite.classes[0].generator.clone();
        let e = o
            .get(&x)
            .unwrap()
            .sample(&x, "batch-1", &seeds(), 1)
            .unwrap_err();
        assert!(e.to_string().contains("--scope v2"), "{e}");
        let mut y = v2.clone();
        y.workload_suite.classes[0].generator = v1.workload_suite.classes[0].generator.clone();
        let e = o
            .get(&y)
            .unwrap()
            .sample(&y, "batch-1", &seeds(), 1)
            .unwrap_err();
        assert!(e.to_string().contains("--scope v1"), "{e}");
        // Fixtures: the v2 public set is pinned by the v2 draft, and its
        // params.bin passes the v2 pin while v1's does not.
        let mut o = o;
        let d = o
            .add_fixtures_dir(&repo().join("oracle/fixtures/v2/public"))
            .unwrap();
        assert_eq!(d, v2.workload_suite.public_fixtures);
        let fx = o.fixtures_for(&v2).unwrap();
        let p = o
            .get(&v2)
            .unwrap()
            .approved_params(&v2, fx.as_deref())
            .unwrap();
        assert!(!p.is_empty());
        let v1fx = repo().join("oracle/fixtures/public");
        let e = o
            .get(&v2)
            .unwrap()
            .approved_params(&v2, Some(&v1fx))
            .unwrap_err();
        assert!(e.to_string().contains("statement_id"), "{e}");
        let cases = o
            .get(&v2)
            .unwrap()
            .fixture_cases(&v2, fx.as_deref().unwrap())
            .unwrap();
        assert_eq!(cases.len(), 25);
        let pin = crate::jobs::RequestPin::from_challenge(&v2).unwrap();
        for c in &cases {
            pin.check(&c.request).unwrap();
            pin.check_claim(&c.expected_claim).unwrap();
        }
    }

    /// v3 is its own registration: fixtures (positives with request = claim,
    /// rejection cases), params pin, generator specs checked for tool and
    /// class; v1/v2 oracles never serve it.
    #[test]
    fn near_v3_oracle_fixtures_rejections_and_generator_pins() {
        let gens = [
            repo().join("spec/workloads/near-transfer-receipt-v1"),
            repo().join("spec/workloads/near-chunk-validation-d0"),
        ];
        let mut o = Oracles::builtin()
            .with_near_dirs(PathBuf::from("/nonexistent/near-arena-oracle"), &gens)
            .unwrap()
            .with_near_v3(PathBuf::from("/nonexistent/near-arena-oracle-v3"), &gens)
            .unwrap();
        let v3 = load("challenges/drafts/near-chunk-validation-d0.draft.json");
        let v1 = load("challenges/chl_5ef2bc7d2068219635426e47ca46bfbb.json");
        assert_eq!(o.get(&v3).unwrap().format(), "near-arena-claim-v3");
        assert_eq!(o.get(&v1).unwrap().format(), "near-arena-claim-v1");
        let d = o
            .add_fixtures_dir(&repo().join("oracle/fixtures/v3/arena-public"))
            .unwrap();
        assert_eq!(d, v3.workload_suite.public_fixtures);
        let fx = o.fixtures_for(&v3).unwrap().unwrap();
        let cases = o.get(&v3).unwrap().fixture_cases(&v3, &fx).unwrap();
        assert_eq!(cases.len(), 78);
        let pin = crate::jobs::RequestPin::from_challenge(&v3).unwrap();
        for c in &cases {
            assert_eq!(c.request, c.expected_claim);
            pin.check_case(&c.request, Some(&c.expected_claim)).unwrap();
        }
        let p = o.get(&v3).unwrap().approved_params(&v3, Some(&fx)).unwrap();
        assert_eq!(p.len(), 99);
        // rejections: public only here (n = 0, no held-out dir configured)
        let r = o.rejection_suite(&v3, &seeds(), 0).unwrap();
        assert_eq!((r.public, r.sampled, r.heldout), (121, 0, 0));
        for c in &r.cases {
            assert!(c.expected_claim.is_empty() && c.public);
            pin.check_case(&c.request, None).unwrap();
        }
        // a v1 generator spec under a v3 class is refused before the binary runs
        let mut x = v3.clone();
        x.workload_suite.classes[0].generator = v1.workload_suite.classes[0].generator.clone();
        let e = o.get(&x).unwrap().sample(&x, &x.workload_suite.classes[0].id.clone(), &seeds(), 1).unwrap_err();
        assert!(e.to_string().contains("near-arena-oracle-v3 gen"), "{e}");
        // a v3 spec of another class is refused
        let mut y = v3.clone();
        y.workload_suite.classes[0].generator = v3.workload_suite.classes[1].generator.clone();
        let e = o.get(&y).unwrap().sample(&y, &y.workload_suite.classes[0].id.clone(), &seeds(), 1).unwrap_err();
        assert!(e.to_string().contains("not \"d0-quiet\""), "{e}");
        // v1 fixtures' params never pass as v3 params
        let e = o
            .get(&v3)
            .unwrap()
            .approved_params(&v3, Some(&repo().join("oracle/fixtures/public")))
            .unwrap_err();
        assert!(e.to_string().contains("format"), "{e}");
    }

    /// With the real oracle binary (`ARENA_TEST_NEAR_ORACLE_V3`): sampled
    /// positives are exactly `n` per class and pass the pin; rejection
    /// sampling alternates out-of-domain chunks and mutants; the committed
    /// held-out set (`ARENA_TEST_HELDOUT_V3`) verifies against the draft.
    #[test]
    fn near_v3_oracle_samples_with_the_real_binary() {
        let Ok(bin) = std::env::var("ARENA_TEST_NEAR_ORACLE_V3") else {
            eprintln!("skipped: ARENA_TEST_NEAR_ORACLE_V3 unset");
            return;
        };
        let gens = [repo().join("spec/workloads/near-chunk-validation-d0")];
        let mut o = Oracles::builtin().with_near_v3(PathBuf::from(bin), &gens).unwrap();
        o.add_fixtures_dir(&repo().join("oracle/fixtures/v3/arena-public")).unwrap();
        let v3 = load("challenges/drafts/near-chunk-validation-d0.draft.json");
        let pin = crate::jobs::RequestPin::from_challenge(&v3).unwrap();
        for c in &v3.workload_suite.classes {
            let got = o.get(&v3).unwrap().sample(&v3, &c.id, &seeds(), 3).unwrap();
            assert_eq!(got.len(), 3);
            for k in &got {
                assert_eq!(k.class.as_deref(), Some(c.id.as_str()));
                assert!(!k.public);
                pin.check_case(&k.request, Some(&k.expected_claim)).unwrap();
            }
        }
        let r = o.rejection_suite(&v3, &seeds(), 6).unwrap();
        assert_eq!((r.public, r.sampled), (121, 6));
        if let Ok(h) = std::env::var("ARENA_TEST_HELDOUT_V3") {
            o.add_heldout_dir(Path::new(&h)).unwrap();
            let s = o.conformance_suite(&v3, &seeds(), 3, true).unwrap();
            assert_eq!(s.heldout, 3);
            let r = o.rejection_suite(&v3, &seeds(), 4).unwrap();
            assert_eq!(r.heldout, 4);
            assert!(r.cases.iter().filter(|c| !c.public).all(|c| !c.id.contains("h1")
                || c.id.starts_with("rejections/") || c.id.starts_with("heldout-reject/")));
        }
    }
}
