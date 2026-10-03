//! Validation and normalization of worker results before they touch the
//! database. Worker output is judge output, but its *shape* is still checked:
//! wrong gates, missing required data or inconsistent benchmark tables are
//! protocol errors (treated as an infrastructure failure of the attempt).

use crate::score::normalize_benchmark;
use arena_db::tier_min;
use arena_jobs::sanitize::{sanitize_line, sanitize_text, MAX_LABEL_BYTES, MAX_NAME_BYTES, MAX_SUMMARY_BYTES};
use arena_jobs::{BuildOutputs, ExecutionInfo, JobKind, JobResult};
use arena_types::{
    challenge::Tier, BenchmarkResult, CandidateManifest, ChallengeDefinition, EvidenceGraph,
    EvidenceRef, GateResult, GateStatus, ObligationId, ReasonCode,
};
use std::collections::HashSet;

pub const MAX_ARTIFACTS: usize = 256;
pub const MAX_GRAPH_ITEMS: usize = 2000;
pub const MAX_REASON_CODES: usize = 32;

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
    /// Every owned gate was reported by the worker with a definite status
    /// (no synthesized or UNKNOWN results): eligible for the formal cache.
    pub definite: bool,
}

pub fn sanitize_evidence(e: &EvidenceRef) -> EvidenceRef {
    EvidenceRef { label: sanitize_line(&e.label, MAX_LABEL_BYTES), digest: e.digest.clone(), public: e.public }
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
        evidence: g.evidence.iter().take(MAX_ARTIFACTS).map(sanitize_evidence).collect(),
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

/// Merge `add` into `base`: nodes keyed by id, edges keyed by (from, to, kind);
/// later results win.
pub fn merge_graphs(base: Option<EvidenceGraph>, add: &EvidenceGraph) -> EvidenceGraph {
    let mut g = base.unwrap_or_default();
    for n in &add.nodes {
        match g.nodes.iter_mut().find(|x| x.id == n.id) {
            Some(x) => *x = n.clone(),
            None => g.nodes.push(n.clone()),
        }
    }
    for e in &add.edges {
        match g.edges.iter_mut().find(|x| x.from == e.from && x.to == e.to && x.kind == e.kind) {
            Some(x) => *x = e.clone(),
            None => g.edges.push(e.clone()),
        }
    }
    g
}

fn server_fail(gate: ObligationId, code: ReasonCode, why: &str, required: &[ObligationId]) -> GateResult {
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
        let mut g = sanitize_gate(g, required);
        if tier_cap == Tier::Demo && !g.reason_codes.contains(&ReasonCode::DemoOnly) {
            g.reason_codes.push(ReasonCode::DemoOnly);
        }
        gates.push(g);
    }
    let mut definite = gates.iter().all(|g| g.status != GateStatus::Unknown);
    for gate in owned {
        if !seen.contains(gate) && required.contains(gate) {
            gates.push(synthesized_unknown(*gate, required, "worker did not report a result for this required gate"));
            definite = false;
        }
    }
    let status_of = |gates: &[GateResult], o: ObligationId| gates.iter().find(|g| g.gate == o).map(|g| g.status);

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
                let m = r.manifest.clone().ok_or("passing VALIDATE result must include the manifest")?;
                let override_reason = if let Err(e) = m.validate() {
                    Some((ReasonCode::ManifestInvalid, format!("manifest failed validation: {e}")))
                } else if m.challenge != challenge_id {
                    Some((ReasonCode::ManifestInvalid, "manifest names a different challenge".to_string()))
                } else if m.security_profile_request != chal.security_profile.id {
                    Some((
                        ReasonCode::ProfileNotAllowed,
                        format!("requested security profile is not {:?}", chal.security_profile.id),
                    ))
                } else {
                    None
                };
                match override_reason {
                    Some((code, why)) => {
                        let i = gates.iter().position(|g| g.gate == ObligationId::PkgWellformed).unwrap();
                        gates[i] = server_fail(ObligationId::PkgWellformed, code, &why, required);
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
                let mut b = r.build.clone().ok_or("passing BUILD result must include build outputs")?;
                b.certificate_decl = sanitize_line(&b.certificate_decl, 256);
                build = Some(b);
            } else if let Some(b) = &r.build {
                // keep diagnostics for failed builds too
                let mut b = b.clone();
                b.certificate_decl = sanitize_line(&b.certificate_decl, 256);
                build = Some(b);
            }
        }
        JobKind::Benchmark => {
            match &r.benchmark {
                Some(b) => benchmark = Some(normalize_benchmark(chal, b.clone())?),
                None if status_of(&gates, ObligationId::Benchmark) == Some(GateStatus::Pass) => {
                    return Err("passing BENCHMARK result must include measurements".into())
                }
                None => {}
            }
        }
        JobKind::FormalCheck | JobKind::Conformance | JobKind::Adversarial => {}
    }
    if kind != JobKind::Benchmark && r.benchmark.is_some() {
        return Err(format!("{kind} job may not report benchmark measurements"));
    }
    Ok(Normalized { gates, tier_cap, manifest, build, benchmark, evidence_graph, artifacts, execution, definite })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn merge_dedupes() {
        use arena_types::evidence::*;
        let n = |id: &str, l: &str| EvidenceNode { id: id.into(), kind: NodeKind::Theorem, label: l.into(), digest: None };
        let e = |s: EdgeStatus| EvidenceEdge {
            from: "a".into(),
            to: "b".into(),
            kind: "refines".into(),
            status: s,
            evidence: vec![],
            note: String::new(),
        };
        let g1 = EvidenceGraph { nodes: vec![n("a", "1"), n("b", "1")], edges: vec![e(EdgeStatus::Missing)] };
        let g2 = EvidenceGraph { nodes: vec![n("a", "2")], edges: vec![e(EdgeStatus::Checked)] };
        let m = merge_graphs(Some(g1), &g2);
        assert_eq!(m.nodes.len(), 2);
        assert_eq!(m.nodes[0].label, "2");
        assert_eq!(m.edges.len(), 1);
        assert_eq!(m.edges[0].status, EdgeStatus::Checked);
    }
}
