//! Validation and normalization of worker results before they touch the
//! database. Worker output is judge output, but its *shape* is still checked:
//! wrong gates, missing required data or inconsistent benchmark tables are
//! protocol errors (treated as an infrastructure failure of the attempt).

use crate::score::normalize_benchmark;
use arena_db::tier_min;
use arena_jobs::sanitize::{
    sanitize_line, sanitize_text, MAX_LABEL_BYTES, MAX_NAME_BYTES, MAX_SUMMARY_BYTES,
};
use arena_jobs::{BuildOutputs, ExecutionInfo, JobKind, JobResult};
use arena_types::{
    challenge::Tier, BenchmarkResult, CandidateManifest, ChallengeDefinition, EvidenceGraph,
    EvidenceRef, GateResult, GateStatus, ObligationId, ReasonCode,
};
use std::collections::HashSet;

pub const MAX_ARTIFACTS: usize = 256;
pub const MAX_GRAPH_ITEMS: usize = 2000;
pub const MAX_REASON_CODES: usize = 32;
pub const MAX_LOG_BYTES: usize = 16 * 1024;

#[derive(Debug, Clone)]
pub struct Normalized {
    pub gates: Vec<GateResult>,
    pub tier_cap: Tier,
    pub manifest: Option<CandidateManifest>,
    pub build: Option<BuildOutputs>,
    pub benchmark: Option<BenchmarkResult>,
    pub evidence_graph: Option<EvidenceGraph>,
    pub artifacts: Vec<EvidenceRef>,
    pub execution: ExecutionInfo,
    pub log_excerpt: Option<String>,
    /// FORMAL_CHECK only: judge-built native verifier (content digest).
    pub native_verifier: Option<arena_types::Digest>,
    /// CONFORMANCE on a coverage-tiered challenge (v1.7): sanitized coverage,
    /// `share_ppm` recomputed by the server.
    pub coverage: Option<arena_types::CoverageReport>,
    /// Every owned gate was reported by the worker with a definite status
    /// (no synthesized or UNKNOWN results): eligible for the formal cache.
    pub definite: bool,
}

pub fn sanitize_evidence(e: &EvidenceRef) -> EvidenceRef {
    EvidenceRef {
        label: sanitize_line(&e.label, MAX_LABEL_BYTES),
        digest: e.digest.clone(),
        public: e.public,
    }
}

pub fn sanitize_gate(g: &GateResult, required: &[ObligationId]) -> GateResult {
    let mut codes: Vec<ReasonCode> = Vec::new();
    for c in &g.reason_codes {
        if !codes.contains(c) && codes.len() < MAX_REASON_CODES {
            codes.push(*c);
        }
    }
    GateResult {
        gate: g.gate,
        mandatory: required.contains(&g.gate),
        status: g.status,
        reason_codes: codes,
        summary: sanitize_text(&g.summary, MAX_SUMMARY_BYTES),
        evidence: g
            .evidence
            .iter()
            .take(MAX_ARTIFACTS)
            .map(sanitize_evidence)
            .collect(),
        started_at: g.started_at.as_deref().map(|s| sanitize_line(s, 64)),
        finished_at: g.finished_at.as_deref().map(|s| sanitize_line(s, 64)),
        // workers cannot claim reuse; only the control plane's cache sets this
        reused_from: None,
    }
}

pub fn sanitize_graph(g: &EvidenceGraph) -> Result<EvidenceGraph, String> {
    if g.nodes.len() > MAX_GRAPH_ITEMS || g.edges.len() > MAX_GRAPH_ITEMS {
        return Err("evidence graph too large".into());
    }
    let mut out = EvidenceGraph::default();
    for n in &g.nodes {
        let mut n = n.clone();
        n.id = sanitize_line(&n.id, MAX_LABEL_BYTES);
        n.label = sanitize_line(&n.label, MAX_LABEL_BYTES);
        out.nodes.push(n);
    }
    for e in &g.edges {
        let mut e = e.clone();
        e.from = sanitize_line(&e.from, MAX_LABEL_BYTES);
        e.to = sanitize_line(&e.to, MAX_LABEL_BYTES);
        e.kind = sanitize_line(&e.kind, 64);
        e.note = sanitize_text(&e.note, 1024);
        e.evidence.truncate(64);
        out.edges.push(e);
    }
    Ok(out)
}

/// Strength of an edge status (weaker = less evidence).
fn strength(s: arena_types::evidence::EdgeStatus) -> u8 {
    use arena_types::evidence::EdgeStatus::*;
    match s {
        Missing => 0,
        Tested => 1,
        Trusted => 2,
        Checked => 3,
    }
}

/// The job kind whose gates own an evidence edge kind (and may therefore
/// establish it). Unknown edge kinds have no owner.
pub fn edge_owner(edge_kind: &str) -> Option<JobKind> {
    match edge_kind {
        "proves"
        | "defined_in"
        | "assumes"
        | "rechecked_by"
        | "contains_candidate_model"
        | "proves_obligations_about"
        | "implements"
        | "built_from"
        | "refines"
        | "binds" => Some(JobKind::FormalCheck),
        "tested_against" => Some(JobKind::Conformance),
        _ => None,
    }
}

/// Merge `add` (reported by a job of kind `source`) into `base`. Nodes are
/// keyed by id (later labels win). Edges, keyed by (from, to, kind), merge
/// **monotonically**: on a conflict the weaker status wins, so a later
/// write can never quietly upgrade an edge; the only upgrade allowed is a
/// MISSING edge becoming established by an edge that carries real evidence
/// (non-empty digests) and comes from the job kind that owns the edge.
pub fn merge_graphs(
    base: Option<EvidenceGraph>,
    add: &EvidenceGraph,
    source: JobKind,
) -> EvidenceGraph {
    use arena_types::evidence::EdgeStatus;
    let mut g = base.unwrap_or_default();
    for n in &add.nodes {
        match g.nodes.iter_mut().find(|x| x.id == n.id) {
            Some(x) => *x = n.clone(),
            None => g.nodes.push(n.clone()),
        }
    }
    for e in &add.edges {
        match g
            .edges
            .iter_mut()
            .find(|x| x.from == e.from && x.to == e.to && x.kind == e.kind)
        {
            Some(x) => {
                let owned_upgrade = x.status == EdgeStatus::Missing
                    && e.status != EdgeStatus::Missing
                    && !e.evidence.is_empty()
                    && edge_owner(&e.kind) == Some(source);
                if owned_upgrade || strength(e.status) <= strength(x.status) {
                    *x = e.clone();
                }
            }
            None => g.edges.push(e.clone()),
        }
    }
    g
}

fn server_fail(
    gate: ObligationId,
    code: ReasonCode,
    why: &str,
    required: &[ObligationId],
) -> GateResult {
    GateResult {
        gate,
        mandatory: required.contains(&gate),
        status: GateStatus::Fail,
        reason_codes: vec![code],
        summary: format!("control plane: {why}"),
        evidence: vec![],
        started_at: None,
        finished_at: None,
        reused_from: None,
    }
}

pub fn synthesized_unknown(gate: ObligationId, required: &[ObligationId], why: &str) -> GateResult {
    GateResult {
        gate,
        mandatory: required.contains(&gate),
        status: GateStatus::Unknown,
        reason_codes: vec![ReasonCode::ObligationUndischarged],
        summary: format!("control plane: {why}"),
        evidence: vec![],
        started_at: None,
        finished_at: None,
        reused_from: None,
    }
}

/// Validate and normalize a worker result for a job of `kind`.
///
/// * `job_tier` is the tier the job was scheduled at (the challenge tier).
/// * `worker_cap` is the worker's registered tier capability.
pub fn check_result(
    kind: JobKind,
    r: &JobResult,
    chal: &ChallengeDefinition,
    challenge_id: &str,
    job_tier: Tier,
    worker_cap: Tier,
) -> Result<Normalized, String> {
    let required = &chal.required_obligations;
    // `mandatory` = blocking (experimental: formal gates are diagnostic).
    let blocking = chal.blocking_obligations();
    let owned = kind.owned_gates();

    // ---- tier cap: min(job tier, worker registration, result's own claim);
    // the namespaces-only dev sandbox is always demo.
    let mut tier_cap = tier_min(job_tier, tier_min(worker_cap, r.execution.tier_cap));
    let backend = sanitize_line(&r.execution.sandbox_backend, 32);
    if backend == "bwrap-dev" {
        tier_cap = Tier::Demo;
    }
    let execution = ExecutionInfo {
        sandbox_backend: backend,
        tier_cap,
        worker_version: sanitize_line(&r.execution.worker_version, MAX_NAME_BYTES),
    };

    // ---- gates
    let mut seen = HashSet::new();
    let mut gates = Vec::new();
    for g in &r.gates {
        if !owned.contains(&g.gate) {
            return Err(format!("{kind} job may not report gate {:?}", g.gate));
        }
        if !seen.insert(g.gate) {
            return Err(format!("duplicate gate {:?}", g.gate));
        }
        let mut g = sanitize_gate(g, &blocking);
        if tier_cap == Tier::Demo && !g.reason_codes.contains(&ReasonCode::DemoOnly) {
            g.reason_codes.push(ReasonCode::DemoOnly);
        }
        gates.push(g);
    }
    let mut definite = gates.iter().all(|g| g.status != GateStatus::Unknown);
    for gate in owned {
        if !seen.contains(gate) && required.contains(gate) {
            gates.push(synthesized_unknown(
                *gate,
                &blocking,
                "worker did not report a result for this required gate",
            ));
            definite = false;
        }
    }
    let status_of = |gates: &[GateResult], o: ObligationId| {
        gates.iter().find(|g| g.gate == o).map(|g| g.status)
    };

    if r.artifacts.len() > MAX_ARTIFACTS {
        return Err("too many artifacts".into());
    }
    let artifacts = r.artifacts.iter().map(sanitize_evidence).collect();
    let evidence_graph = r.evidence_graph.as_ref().map(sanitize_graph).transpose()?;

    // ---- kind-specific payloads
    let mut manifest = None;
    let mut build = None;
    let mut benchmark = None;
    match kind {
        JobKind::Validate => {
            if status_of(&gates, ObligationId::PkgWellformed) == Some(GateStatus::Pass) {
                let m = r
                    .manifest
                    .clone()
                    .ok_or("passing VALIDATE result must include the manifest")?;
                let override_reason = if let Err(e) = m.validate() {
                    Some((
                        ReasonCode::ManifestInvalid,
                        format!("manifest failed validation: {e}"),
                    ))
                } else if m.challenge != challenge_id {
                    Some((
                        ReasonCode::ManifestInvalid,
                        "manifest names a different challenge".to_string(),
                    ))
                } else if let Err(e) = chal.declared_tier(&m) {
                    Some((ReasonCode::ManifestInvalid, e))
                } else if m.security_profile_request != chal.security_profile.id {
                    Some((
                        ReasonCode::ProfileNotAllowed,
                        format!(
                            "requested security profile is not {:?}",
                            chal.security_profile.id
                        ),
                    ))
                } else {
                    None
                };
                match override_reason {
                    Some((code, why)) => {
                        let i = gates
                            .iter()
                            .position(|g| g.gate == ObligationId::PkgWellformed)
                            .unwrap();
                        gates[i] = server_fail(ObligationId::PkgWellformed, code, &why, &blocking);
                    }
                    None => {
                        let mut m = m;
                        m.agent = sanitize_line(&m.agent, 64);
                        m.backend_family = sanitize_line(&m.backend_family, 64);
                        manifest = Some(m);
                    }
                }
            }
        }
        JobKind::Build => {
            if status_of(&gates, ObligationId::BuildReproducible) == Some(GateStatus::Pass) {
                let mut b = r
                    .build
                    .clone()
                    .ok_or("passing BUILD result must include build outputs")?;
                b.certificate_decl = sanitize_line(&b.certificate_decl, 256);
                b.toolchain_image = b.toolchain_image.map(|t| sanitize_line(&t, 128));
                build = Some(b);
            } else if let Some(b) = &r.build {
                // keep diagnostics for failed builds too
                let mut b = b.clone();
                b.certificate_decl = sanitize_line(&b.certificate_decl, 256);
                b.toolchain_image = b.toolchain_image.map(|t| sanitize_line(&t, 128));
                build = Some(b);
            }
        }
        JobKind::Benchmark => match &r.benchmark {
            Some(b) => benchmark = Some(normalize_benchmark(chal, b.clone())?),
            None if status_of(&gates, ObligationId::Benchmark) == Some(GateStatus::Pass) => {
                return Err("passing BENCHMARK result must include measurements".into())
            }
            None => {}
        },
        JobKind::FormalCheck | JobKind::Conformance | JobKind::Adversarial => {}
    }
    if kind != JobKind::FormalCheck && r.native_verifier.is_some() {
        return Err(format!("{kind} job may not report a native verifier"));
    }
    if kind != JobKind::Benchmark && r.benchmark.is_some() {
        return Err(format!("{kind} job may not report benchmark measurements"));
    }
    let coverage = match (&r.coverage, kind, &chal.coverage) {
        (None, _, _) => None,
        (Some(c), JobKind::Conformance, Some(_)) => Some(normalize_coverage(chal, c)?),
        (Some(_), _, _) => {
            return Err(format!(
            "{kind} job may not report coverage (CONFORMANCE on a coverage-tiered challenge only)"
        ))
        }
    };
    let log_excerpt = r
        .log_excerpt
        .as_deref()
        .map(|t| sanitize_text(t, MAX_LOG_BYTES));
    Ok(Normalized {
        gates,
        tier_cap,
        manifest,
        build,
        benchmark,
        evidence_graph,
        artifacts,
        execution,
        log_excerpt,
        native_verifier: r.native_verifier.clone(),
        coverage,
        definite,
    })
}

/// Sanitize a worker's coverage report: the tier must be a tier of the
/// challenge, classes must be workload classes (or the fixtures key), counts
/// must be consistent; `share_ppm` is recomputed from the challenge weights.
/// (The tier is checked against the run's manifest by the orchestrator.)
pub fn normalize_coverage(
    chal: &ChallengeDefinition,
    c: &arena_types::CoverageReport,
) -> Result<arena_types::CoverageReport, String> {
    let spec = chal.coverage.as_ref().ok_or("challenge has no coverage")?;
    if spec.tier(&c.tier).is_none() {
        return Err(format!("coverage names unknown tier {:?}", c.tier));
    }
    let sec = |s: &arena_types::CoverageSection| -> Result<arena_types::CoverageSection, String> {
        let mut out = arena_types::CoverageSection::default();
        for (k, v) in &s.per_class {
            let known = k == arena_types::coverage::FIXTURES_KEY
                || chal.workload_suite.classes.iter().any(|w| &w.id == k);
            if !known {
                return Err(format!("coverage names unknown class {k:?}"));
            }
            if v.proven
                .checked_add(v.abstained)
                .is_none_or(|n| n > v.cases)
            {
                return Err(format!("coverage counts of class {k:?} are inconsistent"));
            }
            out.per_class.insert(k.clone(), v.clone());
        }
        out.finish(chal);
        Ok(out)
    };
    Ok(arena_types::CoverageReport {
        tier: c.tier.clone(),
        conformance: sec(&c.conformance)?,
        heldout: c.heldout.as_ref().map(sec).transpose()?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn merge_dedupes() {
        use arena_types::evidence::*;
        let n = |id: &str, l: &str| EvidenceNode {
            id: id.into(),
            kind: NodeKind::Theorem,
            label: l.into(),
            digest: None,
        };
        let e = |s: EdgeStatus| EvidenceEdge {
            from: "a".into(),
            to: "b".into(),
            kind: "refines".into(),
            status: s,
            evidence: vec![],
            note: String::new(),
        };
        let g1 = EvidenceGraph {
            nodes: vec![n("a", "1"), n("b", "1")],
            edges: vec![e(EdgeStatus::Missing)],
        };
        let g2 = EvidenceGraph {
            nodes: vec![n("a", "2")],
            edges: vec![e(EdgeStatus::Checked)],
        };
        // No evidence: MISSING is never upgraded.
        let m = merge_graphs(Some(g1.clone()), &g2, JobKind::FormalCheck);
        assert_eq!(m.nodes.len(), 2);
        assert_eq!(m.nodes[0].label, "2");
        assert_eq!(m.edges.len(), 1);
        assert_eq!(m.edges[0].status, EdgeStatus::Missing);
        // With evidence, from the owning job kind: upgraded.
        let mut g3 = g2.clone();
        g3.edges[0].evidence = vec![arena_types::Digest::of_bytes(b"proof")];
        let m = merge_graphs(Some(g1.clone()), &g3, JobKind::FormalCheck);
        assert_eq!(m.edges[0].status, EdgeStatus::Checked);
        // ...but not from another job kind.
        let m = merge_graphs(Some(g1), &g3, JobKind::Benchmark);
        assert_eq!(m.edges[0].status, EdgeStatus::Missing);
        // Weaker status wins on conflict: CHECKED then TESTED -> TESTED; a
        // later CHECKED cannot raise it back.
        let checked = EvidenceGraph {
            nodes: vec![],
            edges: vec![g3.edges[0].clone()],
        };
        let mut tested = checked.clone();
        tested.edges[0].status = EdgeStatus::Tested;
        let m = merge_graphs(Some(checked.clone()), &tested, JobKind::Conformance);
        assert_eq!(m.edges[0].status, EdgeStatus::Tested);
        let m = merge_graphs(Some(m), &checked, JobKind::FormalCheck);
        assert_eq!(m.edges[0].status, EdgeStatus::Tested);
    }

    #[test]
    fn coverage_is_sanitized_and_share_recomputed() {
        let mut c: ChallengeDefinition = serde_json::from_str(include_str!(
            "../../../challenges/chl_4b4316516128000f129cff9b3ced8b51.json"
        ))
        .unwrap();
        c.coverage = Some(arena_types::CoverageSpec {
            version: "coverage-v1".into(),
            statement_spec: "S".into(),
            soundness_lift: "L".into(),
            tiers: vec![arena_types::CoverageTier {
                id: "D0".into(),
                rank: 0,
                params: "P".into(),
                classes: vec![],
            }],
        });
        let mut sec = arena_types::CoverageSection::default();
        sec.record(Some("d0-quiet"), true, false);
        sec.record(Some("d0-missing"), false, true);
        sec.share_ppm = 999_999; // forged
        let rep = arena_types::CoverageReport {
            tier: "D0".into(),
            conformance: sec.clone(),
            heldout: None,
        };
        let n = normalize_coverage(&c, &rep).unwrap();
        let mut want = sec.clone();
        want.finish(&c);
        assert_eq!(n.conformance.share_ppm, want.share_ppm);
        assert!(n.conformance.share_ppm < 999_999);
        let mut bad = rep.clone();
        bad.tier = "D7".into();
        assert!(normalize_coverage(&c, &bad).is_err());
        let mut bad = rep.clone();
        bad.conformance
            .per_class
            .get_mut("d0-quiet")
            .unwrap()
            .proven = 5;
        assert!(normalize_coverage(&c, &bad)
            .unwrap_err()
            .contains("inconsistent"));
        let mut bad = rep;
        bad.conformance
            .per_class
            .insert("no-such-class".into(), Default::default());
        assert!(normalize_coverage(&c, &bad).is_err());
    }
}
