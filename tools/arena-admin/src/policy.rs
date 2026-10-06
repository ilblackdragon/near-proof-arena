//! Governance policy checks on a `ChallengeDefinition`.
//!
//! These are the rules a definition must satisfy before it can be signed and
//! that every verifier re-checks. Errors block signing/loading; warnings are
//! printed but do not block.

use crate::governed::GovernedSet;
use arena_types::challenge::{ChallengeDefinition, ScopeKind, Tier};
use arena_types::security::Privacy;
use arena_types::{Digest, ObligationId};
use std::collections::BTreeSet;

pub const CHALLENGE_SCHEMA: &str = "arena-challenge-v1";
pub const WEIGHT_TOTAL_PPM: u64 = 1_000_000;

/// Lean axioms that may ever appear in an allowlist. Anything else
/// (`sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, user axioms) is
/// forbidden; cryptographic assumptions enter only as hypotheses pinned by
/// `security/assumptions/*.json`, never as axioms.
pub const STANDARD_AXIOMS: &[&str] = &["propext", "Classical.choice", "Quot.sound"];

pub const ALL_OBLIGATIONS: &[ObligationId] = &[
    ObligationId::PkgWellformed,
    ObligationId::BuildReproducible,
    ObligationId::ArtifactBinding,
    ObligationId::FormalSemanticSoundness,
    ObligationId::FormalSemanticCompleteness,
    ObligationId::FormalCryptoSoundness,
    ObligationId::FormalImplConnection,
    ObligationId::FormalZk,
    ObligationId::AxiomAudit,
    ObligationId::ConformanceDifferential,
    ObligationId::AdversarialProofs,
    ObligationId::ProverReliability,
    ObligationId::ResourceLimits,
    ObligationId::Benchmark,
];

/// Minimum obligations of an `experimental` challenge. `ARTIFACT_BINDING` is
/// required so the judge always evaluates and reports it, but on experimental
/// tier it (like every formal obligation) is **diagnostic**: the server never
/// lets it block the conformance / adversarial / benchmark stages and never
/// lets it enter the decision (`ChallengeDefinition::blocking_obligations`).
/// Experimental runs are never ranked and never formally accepted.
pub const EXPERIMENTAL_MIN: &[ObligationId] = &[
    ObligationId::PkgWellformed,
    ObligationId::BuildReproducible,
    ObligationId::ArtifactBinding,
    ObligationId::ConformanceDifferential,
    ObligationId::AdversarialProofs,
    ObligationId::ProverReliability,
    ObligationId::ResourceLimits,
];

pub const DEMO_MIN: &[ObligationId] = &[ObligationId::PkgWellformed];

#[derive(Debug, Default, Clone)]
pub struct Findings {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl Findings {
    pub fn ok(&self) -> bool {
        self.errors.is_empty()
    }
    fn err(&mut self, s: impl Into<String>) {
        self.errors.push(s.into());
    }
    fn warn(&mut self, s: impl Into<String>) {
        self.warnings.push(s.into());
    }
    pub fn extend(&mut self, o: Findings) {
        self.errors.extend(o.errors);
        self.warnings.extend(o.warnings);
    }
}

/// `sha256:000…0` — the explicit "not yet available" placeholder. Allowed
/// only in `demo` tier.
pub fn zero_digest() -> Digest {
    Digest::try_from(format!("sha256:{}", "0".repeat(64))).unwrap()
}

fn is_hex(s: &str, len: usize) -> bool {
    s.len() == len && s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

pub fn valid_challenge_id(s: &str) -> bool {
    s.strip_prefix("chl_").is_some_and(|h| is_hex(h, 32))
}

pub fn required_for(tier: Tier, privacy: Privacy) -> Vec<ObligationId> {
    match tier {
        Tier::Formal => ALL_OBLIGATIONS
            .iter()
            .copied()
            .filter(|o| !(*o == ObligationId::FormalZk && privacy == Privacy::ValidityOnly))
            .collect(),
        Tier::Experimental => EXPERIMENTAL_MIN.to_vec(),
        Tier::Demo => DEMO_MIN.to_vec(),
    }
}

pub fn check_definition(def: &ChallengeDefinition, gov: &GovernedSet) -> Findings {
    let mut f = Findings::default();
    let tier = def.tier;

    if def.schema != CHALLENGE_SCHEMA {
        f.err(format!(
            "schema must be {CHALLENGE_SCHEMA:?}, got {:?}",
            def.schema
        ));
    }
    if def.name.is_empty()
        || def.name.len() > 64
        || !def
            .name
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
    {
        f.err("name must match [a-z0-9-]{1,64}");
    }
    if def.season.trim().is_empty() {
        f.err("season must be non-empty");
    }
    match time::OffsetDateTime::parse(
        &def.created_at,
        &time::format_description::well_known::Rfc3339,
    ) {
        Ok(t) if t.offset().is_utc() => {}
        _ => f.err("created_at must be an RFC 3339 timestamp in UTC (…Z)"),
    }

    // --- nearcore pin ---------------------------------------------------
    if !def.nearcore.repo.starts_with("https://") {
        f.err("nearcore.repo must be an https URL");
    }
    if !is_hex(&def.nearcore.commit, 40) {
        f.err("nearcore.commit must be a full 40-char lowercase commit hash");
    }
    if def.nearcore.tag.trim().is_empty() {
        f.err("nearcore.tag must be non-empty");
    }
    if def.protocol_version == 0 {
        f.err("protocol_version must be set");
    }

    // --- placeholders -----------------------------------------------------
    let zero = zero_digest();
    let mut digests: Vec<(&str, &Digest)> = vec![
        ("runtime_config_digest", &def.runtime_config_digest),
        (
            "semantic_scope.formal_spec.tree_digest",
            &def.semantic_scope.formal_spec.tree_digest,
        ),
        (
            "semantic_scope.spec_doc_digest",
            &def.semantic_scope.spec_doc_digest,
        ),
        (
            "claim_encoding.spec_digest",
            &def.claim_encoding.spec_digest,
        ),
        (
            "toolchain_policy.checker_image",
            &def.toolchain_policy.checker_image,
        ),
        (
            "workload_suite.public_fixtures",
            &def.workload_suite.public_fixtures,
        ),
        (
            "workload_suite.heldout_commitment",
            &def.workload_suite.heldout_commitment,
        ),
    ];
    for c in &def.workload_suite.classes {
        digests.push(("workload_suite.classes[].generator", &c.generator));
    }
    for (name, d) in digests {
        if *d == zero {
            if tier == Tier::Demo {
                f.warn(format!(
                    "{name} is the all-zero placeholder (allowed in demo tier only)"
                ));
            } else {
                f.err(format!(
                    "{name} is the all-zero placeholder; not allowed in {tier:?} tier"
                ));
            }
        }
    }

    // --- semantic scope ---------------------------------------------------
    let s = &def.semantic_scope;
    if s.kind == ScopeKind::Subset && s.restrictions.is_empty() {
        f.err("subset scope must list its restrictions");
    }
    let mut rids = BTreeSet::new();
    for r in &s.restrictions {
        if r.id.is_empty() || r.text.trim().is_empty() || !rids.insert(&r.id) {
            f.err(format!(
                "restriction {:?}: id must be unique and non-empty, text non-empty",
                r.id
            ));
        }
    }
    if s.excludes.is_empty() {
        f.warn(
            "semantic_scope.excludes is empty: state explicitly which properties are NOT proven",
        );
    }
    if s.formal_spec.lean_toolchain != def.toolchain_policy.lean_toolchain {
        f.err("formal_spec.lean_toolchain must equal toolchain_policy.lean_toolchain");
    }

    // --- claim encoding ---------------------------------------------------
    let ce = &def.claim_encoding;
    // (max_witness_bytes may be 0: relations with an empty witness)
    if ce.format.is_empty() || ce.max_claim_bytes == 0 || ce.max_request_bytes == 0 {
        f.err("claim_encoding: format, max_claim_bytes and max_request_bytes must be set");
    }

    // --- security profile -------------------------------------------------
    let prof = &def.security_profile;
    match gov.profiles.get(&prof.id) {
        None => f.err(format!("security_profile {:?} is not a governed profile", prof.id)),
        Some(g) if g != prof => f.err(format!(
            "security_profile {:?} differs from governed security/profiles/{}.json (profiles must be copied verbatim)",
            prof.id, prof.id
        )),
        Some(_) => {}
    }
    for a in &prof.allowed_assumptions {
        match gov.assumptions.get(a) {
            None => f.err(format!("assumption {a:?} is not governed")),
            Some(asm) if asm.lean_decl_digest.is_none() => {
                if tier == Tier::Formal {
                    f.err(format!(
                        "assumption {a:?} has no pinned lean_decl_digest; formal challenges require every \
                         allowed assumption to be pinned to an exact formal-core declaration"
                    ))
                } else {
                    f.warn(format!(
                        "assumption {a:?} not yet pinned (lean_decl_digest = null)"
                    ))
                }
            }
            Some(_) => {}
        }
    }
    if tier == Tier::Formal && prof.target_bits < 128 {
        f.err("formal tier requires target_bits >= 128");
    }

    // --- toolchain policy -------------------------------------------------
    let tp = &def.toolchain_policy;
    for ax in &tp.axiom_allowlist {
        if !STANDARD_AXIOMS.contains(&ax.as_str()) {
            f.err(format!(
                "axiom {ax:?} is not allowed in any allowlist (only {STANDARD_AXIOMS:?}); \
                 assumptions enter as hypotheses, never axioms"
            ));
        }
    }
    let mut pk = BTreeSet::new();
    for (name, commit) in &tp.allowed_packages {
        if !pk.insert(name) {
            f.err(format!("allowed_packages: duplicate {name:?}"));
        }
        if !is_hex(commit, 40) {
            f.err(format!(
                "allowed_packages[{name}] must pin a full 40-char commit"
            ));
        }
    }
    // --- formal admission-statement parameters ---------------------------------
    match &def.formal_params {
        None if tier == Tier::Formal => f.err(
            "formal tier requires formal_params {verify_fuel, max_proof_bytes, max_reduction_fuel}",
        ),
        None => {}
        Some(fp) => {
            if fp.verify_fuel == 0 || fp.max_reduction_fuel == 0 {
                f.err("formal_params.verify_fuel and max_reduction_fuel must be non-zero");
            }
            if fp.max_proof_bytes != def.resource_limits.max_proof_bytes {
                f.err("formal_params.max_proof_bytes must equal resource_limits.max_proof_bytes");
            }
        }
    }
    // --- scoring (v1.5): cost_v1 pins a price model by digest ----------------
    if let Err(e) = def.check_scoring() {
        f.err(format!("scoring: {e}"));
    }
    // --- coverage tiers (v1.7, CONTRACTS §11) ---------------------------------
    if let Err(e) = def.check_coverage() {
        f.err(format!("coverage: {e}"));
    }
    if tier == Tier::Formal {
        if tp.recheckers.is_empty() {
            f.err("formal tier requires at least one independent kernel rechecker");
        } else if tp.recheckers.len() < 2 {
            f.warn(
                "formal tier with a single rechecker; two independent recheckers are recommended",
            );
        }
    }

    // --- obligations -------------------------------------------------------
    let req: BTreeSet<_> = def.required_obligations.iter().copied().collect();
    let na: BTreeSet<_> = def.not_applicable_gates.iter().copied().collect();
    if req.len() != def.required_obligations.len() {
        f.err("required_obligations contains duplicates");
    }
    if na.len() != def.not_applicable_gates.len() {
        f.err("not_applicable_gates contains duplicates");
    }
    for o in req.intersection(&na) {
        f.err(format!("{o:?} is both required and not-applicable"));
    }
    for o in &na {
        if *o != ObligationId::FormalZk {
            f.err(format!(
                "{o:?} may not be declared not-applicable (only FORMAL_ZK, for validity_only)"
            ));
        }
    }
    match prof.privacy {
        Privacy::ValidityOnly => {
            if !na.contains(&ObligationId::FormalZk) {
                f.err("validity_only profile: FORMAL_ZK must be listed in not_applicable_gates");
            }
            if req.contains(&ObligationId::FormalZk) {
                f.err("validity_only profile: FORMAL_ZK must not be required");
            }
        }
        Privacy::ZeroKnowledge => {
            // (formal tier additionally requires FORMAL_ZK via `required_for`)
            if na.contains(&ObligationId::FormalZk) {
                f.err("zero_knowledge profile: FORMAL_ZK may not be not-applicable");
            }
        }
    }
    for o in required_for(tier, prof.privacy) {
        if !req.contains(&o) {
            f.err(format!("{tier:?} tier must require {o:?}"));
        }
    }
    let diagnostic = def.diagnostic_obligations();
    if !diagnostic.is_empty() {
        f.warn(format!(
            "experimental tier: {diagnostic:?} are diagnostic (evaluated and reported, never blocking, \
             never in the decision; no rank, no formal acceptance)"
        ));
    }

    // --- hardware / workloads / measurement --------------------------------
    let hw = &def.hardware_profile;
    if hw.id.is_empty() || hw.vcpus == 0 || hw.ram_bytes == 0 {
        f.err("hardware_profile: id, vcpus, ram_bytes must be set");
    }
    if hw.gpu.is_none() && def.resource_limits.max_vram_bytes != 0 {
        f.warn("max_vram_bytes > 0 but hardware profile has no GPU");
    }
    let ws = &def.workload_suite;
    if ws.revision.is_empty() {
        f.err("workload_suite.revision must be set");
    }
    if ws.classes.is_empty() {
        f.err("workload_suite must have at least one class");
    }
    let total: u64 = ws.classes.iter().map(|c| c.weight_ppm as u64).sum();
    if total != WEIGHT_TOTAL_PPM {
        f.err(format!(
            "workload weights sum to {total} ppm, must be exactly {WEIGHT_TOTAL_PPM}"
        ));
    }
    let mut cids = BTreeSet::new();
    for c in &ws.classes {
        if !cids.insert(c.id.as_str()) {
            f.err(format!("duplicate workload class {:?}", c.id));
        }
        if c.weight_ppm == 0 || c.batch_size == 0 {
            f.err(format!(
                "class {:?}: weight_ppm and batch_size must be > 0",
                c.id
            ));
        }
    }
    let mut bids = BTreeSet::new();
    for (cid, ns) in &ws.baseline_ns {
        if !cids.contains(cid.as_str()) {
            f.err(format!("baseline_ns for unknown class {cid:?}"));
        }
        if !bids.insert(cid.as_str()) {
            f.err(format!("duplicate baseline_ns entry for {cid:?}"));
        }
        if *ns == 0 {
            f.err(format!("baseline_ns[{cid}] must be > 0"));
        }
    }
    if bids.len() != cids.len() {
        let msg = "baseline_ns does not cover every workload class (score undefined)";
        let unmeasured = ws.baseline_ns.is_empty() && ws.baseline_submission.is_none();
        if tier == Tier::Formal && !unmeasured {
            f.err(msg);
        } else if unmeasured {
            // A formal challenge may be frozen before its reference backend is
            // measured: admission is decided, but scores stay null until a
            // superseding challenge pins baselines for every class.
            f.warn("no baseline yet (baseline_submission = null, baseline_ns = []): admissions are decided but scores are null until a superseding challenge pins baselines");
        } else {
            f.warn(msg);
        }
    }
    let m = &def.measurement;
    if m.aggregation != "median" {
        f.err("measurement.aggregation must be \"median\" in v1");
    }
    if m.measured_runs == 0 || m.per_run_timeout_ms == 0 || m.concurrency == 0 {
        f.err("measurement: measured_runs, per_run_timeout_ms, concurrency must be > 0");
    }
    if tier == Tier::Formal && m.measured_runs < 5 {
        f.err("formal tier requires measured_runs >= 5");
    }
    let rl = &def.resource_limits;
    for (n, v) in [
        ("max_proof_bytes", rl.max_proof_bytes),
        ("max_verify_ms", rl.max_verify_ms),
        ("max_prove_ms", rl.max_prove_ms),
        ("max_ram_bytes", rl.max_ram_bytes),
        ("max_public_artifact_bytes", rl.max_public_artifact_bytes),
        ("max_prepare_ms", rl.max_prepare_ms),
        ("max_build_ms", rl.max_build_ms),
    ] {
        if v == 0 {
            f.err(format!("resource_limits.{n} must be > 0"));
        }
    }

    if let Some(prev) = &def.supersedes {
        if !valid_challenge_id(prev) {
            f.err(format!("supersedes {prev:?} is not a challenge id"));
        }
    }
    f
}
