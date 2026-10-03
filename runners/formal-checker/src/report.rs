//! Gate assembly, evidence graph fragment and report types.

use crate::findings::{is_axiom_code, Finding, Scope, Severity};
use arena_types::evidence::{EdgeStatus, EvidenceEdge, EvidenceNode, NodeKind};
use arena_types::{
    Digest, EvidenceGraph, EvidenceRef, GateResult, GateStatus, ObligationId, ReasonCode,
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GateSpec {
    pub gate: ObligationId,
    pub mandatory: bool,
}

pub fn default_gates() -> Vec<GateSpec> {
    use ObligationId::*;
    [
        FormalSemanticSoundness,
        FormalSemanticCompleteness,
        FormalCryptoSoundness,
        FormalImplConnection,
        AxiomAudit,
    ]
    .into_iter()
    .map(|gate| GateSpec {
        gate,
        mandatory: true,
    })
    .collect()
}

#[derive(Clone, Debug, Serialize)]
pub struct RecheckerRun {
    /// `leanchecker`, `nanoda`, `lean4lean`, `arena-audit`, `ndjson-audit`.
    pub id: String,
    pub ran: bool,
    /// `accepted` | `rejected` | `timeout` | `error` | `not_run`
    pub verdict: String,
    pub wall_ms: u64,
    pub detail: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct Timing {
    pub step: String,
    pub wall_ms: u64,
}

#[derive(Clone, Debug, Serialize)]
pub struct ClosureReport {
    pub certificate: String,
    pub count: usize,
    pub digest: Option<Digest>,
    pub axioms: Vec<String>,
    /// Evidence file listing (name, kind, decl hash) for the whole closure.
    pub listing: Option<EvidenceRef>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ModelReport {
    pub decl: String,
    pub module: String,
    /// Digest of the model's dependency closure (name, decl hash).
    pub closure_digest: Option<Digest>,
    pub axioms: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct FormalCheckReport {
    pub schema: &'static str,
    pub cache_key: Digest,
    pub lean_toolchain: String,
    pub runner: String,
    /// `Some(demo)` when produced through a dev runner.
    pub tier_cap: Option<arena_types::challenge::Tier>,
    pub gates: Vec<GateResult>,
    pub findings: Vec<Finding>,
    pub rechecks: Vec<RecheckerRun>,
    pub closure: Option<ClosureReport>,
    pub evidence: Vec<EvidenceRef>,
    pub evidence_graph: EvidenceGraph,
    /// native-lean route: the judge-built verifier executable.
    pub native_verifier: Option<crate::native::NativeVerifierBuild>,
    /// native-lean route: the candidate verifier model inside the statement.
    pub model: Option<ModelReport>,
    pub warnings: Vec<String>,
    pub timings: Vec<Timing>,
}

fn gate_relevant(g: ObligationId, f: &Finding, conjunct_gates: Option<&[ObligationId]>) -> bool {
    if g == ObligationId::ArtifactBinding {
        // The binding of the executed verifier to the statement: fails on
        // binding findings; undecided whenever anything is undecided.
        return f.code == ReasonCode::ArtifactBindingFailed || f.severity == Severity::Unknown;
    }
    if f.scope == Scope::Binding {
        return false;
    }
    if g == ObligationId::AxiomAudit {
        // Conservative: if there is no valid certificate (wrong statement,
        // missing, not rechecked, ...) there is nothing whose axioms passed.
        return true;
    }
    match f.scope {
        Scope::All => true,
        Scope::Certificate => true,
        Scope::Conjunct(i) => match conjunct_gates {
            Some(cg) => cg.get(i) == Some(&g),
            None => true,
        },
        Scope::Binding => false,
    }
}

pub fn assemble_gates(
    specs: &[GateSpec],
    findings: &[Finding],
    conjunct_gates: Option<&[ObligationId]>,
    evidence: &[EvidenceRef],
    started_at: &str,
    finished_at: &str,
) -> Vec<GateResult> {
    specs
        .iter()
        .map(|s| {
            let rel: Vec<&Finding> = findings.iter().filter(|f| gate_relevant(s.gate, f, conjunct_gates)).collect();
            let fails: Vec<&&Finding> = rel.iter().filter(|f| f.severity == Severity::Fail).collect();
            let unknowns: Vec<&&Finding> = rel.iter().filter(|f| f.severity == Severity::Unknown).collect();
            let (status, chosen): (GateStatus, Vec<&&Finding>) = if !fails.is_empty() {
                (GateStatus::Fail, fails)
            } else if !unknowns.is_empty() {
                (GateStatus::Unknown, unknowns)
            } else {
                (GateStatus::Pass, vec![])
            };
            let mut codes: Vec<ReasonCode> = Vec::new();
            for f in &chosen {
                if !codes.contains(&f.code) {
                    codes.push(f.code);
                }
            }
            let summary = match status {
                GateStatus::Pass => match s.gate {
                    ObligationId::ArtifactBinding => "verifier executable is the judge's build of the certified Lean model; its digest is pinned in the statement (binary↔model edge: trusted Lean compiler/runtime)".to_string(),
                    ObligationId::AxiomAudit => "certified closure uses only allowlisted axioms; no sorry/native shortcuts".to_string(),
                    _ => "certificate type equals the judge-constructed statement; kernel rechecks accepted".to_string(),
                },
                _ => crate::findings::bound(chosen.iter().map(|f| f.detail.as_str()).collect::<Vec<_>>().join("\n")),
            };
            GateResult {
                gate: s.gate,
                mandatory: s.mandatory,
                status,
                reason_codes: codes,
                summary,
                evidence: evidence.to_vec(),
                started_at: Some(started_at.to_string()),
                finished_at: Some(finished_at.to_string()),
                reused_from: None,
            }
        })
        .collect()
}

pub struct GraphInput<'a> {
    pub certificate: &'a str,
    pub certificate_digest: Option<Digest>,
    pub statement_digest: Option<Digest>,
    pub trusted: &'a [(String, Digest)],
    pub axioms: &'a [String],
    pub allowlist: &'a [String],
    pub rechecks: &'a [RecheckerRun],
    pub type_ok: bool,
    pub evidence: Vec<Digest>,
    pub toolchain_digest: Digest,
    pub model: Option<&'a ModelReport>,
    pub native: Option<&'a crate::native::NativeVerifierBuild>,
    /// Approved-interpreter route (`.interp d`): `d` = sha256 of the verifier
    /// bytecode the statement pins (FORMAL_INTERFACE §4(a), status *checked*).
    pub interp: Option<Digest>,
}

pub fn evidence_graph(g: &GraphInput) -> EvidenceGraph {
    let mut nodes = vec![
        EvidenceNode {
            id: "formal:certificate".into(),
            kind: NodeKind::Theorem,
            label: format!("certificate {}", g.certificate),
            digest: g.certificate_digest.clone(),
        },
        EvidenceNode {
            id: "formal:expected_statement".into(),
            kind: NodeKind::Theorem,
            label: "judge-constructed admission statement".into(),
            digest: g.statement_digest.clone(),
        },
        EvidenceNode {
            id: "tcb:lean_toolchain".into(),
            kind: NodeKind::TcbComponent,
            label: format!("Lean {}", crate::toolchain::lean_toolchain()),
            digest: Some(g.toolchain_digest.clone()),
        },
    ];
    let mut edges = vec![EvidenceEdge {
        from: "formal:certificate".into(),
        to: "formal:expected_statement".into(),
        kind: "proves".into(),
        status: if g.type_ok {
            EdgeStatus::Checked
        } else {
            EdgeStatus::Missing
        },
        evidence: g.evidence.clone(),
        note: "syntactic Expr equality of the certificate type and the reference statement".into(),
    }];
    for (name, d) in g.trusted {
        let id = format!("formal:trusted:{name}");
        nodes.push(EvidenceNode {
            id: id.clone(),
            kind: NodeKind::FormalSemantics,
            label: name.clone(),
            digest: Some(d.clone()),
        });
        edges.push(EvidenceEdge {
            from: "formal:expected_statement".into(),
            to: id,
            kind: "defined_in".into(),
            status: EdgeStatus::Trusted,
            evidence: vec![d.clone()],
            note: "judge-pinned module; candidate copies must be hash-identical".into(),
        });
    }
    for ax in g.axioms {
        let id = format!("formal:axiom:{ax}");
        nodes.push(EvidenceNode {
            id: id.clone(),
            kind: NodeKind::Assumption,
            label: ax.clone(),
            digest: None,
        });
        let ok = g.allowlist.contains(ax);
        edges.push(EvidenceEdge {
            from: "formal:certificate".into(),
            to: id,
            kind: "assumes".into(),
            status: if ok {
                EdgeStatus::Trusted
            } else {
                EdgeStatus::Missing
            },
            evidence: vec![],
            note: if ok {
                "allowlisted axiom".into()
            } else {
                "axiom NOT in the challenge allowlist".into()
            },
        });
    }
    for r in g.rechecks {
        let id = format!("tcb:{}", r.id);
        nodes.push(EvidenceNode {
            id: id.clone(),
            kind: NodeKind::TcbComponent,
            label: r.id.clone(),
            digest: None,
        });
        edges.push(EvidenceEdge {
            from: "formal:certificate".into(),
            to: id,
            kind: "rechecked_by".into(),
            status: if r.verdict == "accepted" {
                EdgeStatus::Checked
            } else {
                EdgeStatus::Missing
            },
            evidence: vec![],
            note: format!(
                "{} ({})",
                r.verdict,
                r.detail.chars().take(200).collect::<String>()
            ),
        });
    }
    if let Some(m) = g.model {
        nodes.push(EvidenceNode {
            id: "formal:verifier_model".into(),
            kind: NodeKind::BackendSemantics,
            label: format!(
                "candidate-defined verifier model {} (inside the admission statement)",
                m.decl
            ),
            digest: m.closure_digest.clone(),
        });
        edges.push(EvidenceEdge {
            from: "formal:expected_statement".into(),
            to: "formal:verifier_model".into(),
            kind: "contains_candidate_model".into(),
            status: if g.type_ok { EdgeStatus::Checked } else { EdgeStatus::Missing },
            evidence: m.closure_digest.iter().cloned().collect(),
            note: "statement instantiated at the candidate model; model closure audited (axioms, no sorry/native/partial/unsafe/extern, no shadowing)".into(),
        });
        edges.push(EvidenceEdge {
            from: "formal:certificate".into(),
            to: "formal:verifier_model".into(),
            kind: "proves_obligations_about".into(),
            status: if g.type_ok {
                EdgeStatus::Checked
            } else {
                EdgeStatus::Missing
            },
            evidence: vec![],
            note: "semantic/crypto/completeness obligations are kernel-checked about this model"
                .into(),
        });
    }
    if let Some(n) = g.native {
        nodes.push(EvidenceNode {
            id: "artifact:verifier_binary".into(),
            kind: NodeKind::Artifact,
            label: format!("judge-built native verify ({})", n.toolchain_id),
            digest: Some(n.digest.clone()),
        });
        nodes.push(EvidenceNode {
            id: "tcb:lean_compiler_runtime".into(),
            kind: NodeKind::TcbComponent,
            label: format!("Lean compiler + runtime {}", n.lean_toolchain),
            digest: Some(g.toolchain_digest.clone()),
        });
        edges.push(EvidenceEdge {
            from: "artifact:verifier_binary".into(),
            to: "formal:verifier_model".into(),
            kind: "implements".into(),
            status: EdgeStatus::Trusted,
            evidence: vec![n.digest.clone()],
            note: "compiled by the judge from the model with the governed Lean compiler; NOT a checked edge".into(),
        });
        edges.push(EvidenceEdge {
            from: "artifact:verifier_binary".into(),
            to: "tcb:lean_compiler_runtime".into(),
            kind: "built_from".into(),
            status: EdgeStatus::Trusted,
            evidence: vec![g.toolchain_digest.clone()],
            note: "trusted-base entry".into(),
        });
    }
    if let Some(d) = &g.interp {
        nodes.push(EvidenceNode {
            id: "artifact:verifier_bytecode".into(),
            kind: NodeKind::Artifact,
            label: "verifier bytecode (NPAI v1 image) run by the judge's interpreter".into(),
            digest: Some(d.clone()),
        });
        nodes.push(EvidenceNode {
            id: "tcb:npai_interpreter".into(),
            kind: NodeKind::TcbComponent,
            label: "judge NPAI interpreter (npai-verify) vs ArenaCore.Interp (TCB#8)".into(),
            digest: None,
        });
        // FORMAL_IMPL_CONNECTION on route (a): the statement is about
        // `interpOracleVerifier code fuel` with `sha256 code = d`, so the
        // kernel-checked certificate is about exactly this image.
        edges.push(EvidenceEdge {
            from: "artifact:verifier_bytecode".into(),
            to: "formal:expected_statement".into(),
            kind: "implements".into(),
            status: if g.type_ok {
                EdgeStatus::Checked
            } else {
                EdgeStatus::Missing
            },
            evidence: vec![d.clone()],
            note: "approved-interpreter route: the statement pins `.interp sha256(bytecode)` and the certificate proves the obligations about `interpOracleVerifier` on this exact image (kernel-checked; no compiler involved)".into(),
        });
        edges.push(EvidenceEdge {
            from: "artifact:verifier_bytecode".into(),
            to: "tcb:npai_interpreter".into(),
            kind: "executed_by".into(),
            status: EdgeStatus::Tested,
            evidence: vec![d.clone()],
            note: "interpreter agreement with ArenaCore.Interp is differentially tested, not checked (TCB#8)".into(),
        });
    }
    EvidenceGraph { nodes, edges }
}

/// Lightweight helper to dedupe findings by (code, scope, detail).
pub fn dedupe(f: Vec<Finding>) -> Vec<Finding> {
    let mut out: Vec<Finding> = Vec::new();
    for x in f {
        if !out
            .iter()
            .any(|y| y.code == x.code && y.scope == x.scope && y.detail == x.detail)
        {
            out.push(x);
        }
    }
    out
}

pub fn has_fail(f: &[Finding]) -> bool {
    f.iter().any(|x| x.severity == Severity::Fail)
}

pub fn axiom_codes(f: &[Finding]) -> Vec<ReasonCode> {
    f.iter()
        .filter(|x| is_axiom_code(x.code))
        .map(|x| x.code)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use arena_types::evidence::EdgeStatus;

    fn graph(type_ok: bool, interp: Option<Digest>) -> EvidenceGraph {
        evidence_graph(&GraphInput {
            certificate: "C.certificate",
            certificate_digest: None,
            statement_digest: None,
            trusted: &[],
            axioms: &[],
            allowlist: &[],
            rechecks: &[],
            type_ok,
            evidence: vec![],
            toolchain_digest: Digest::of_bytes(b"tc"),
            model: None,
            native: None,
            interp,
        })
    }

    fn impl_edge(g: &EvidenceGraph) -> Option<&EvidenceEdge> {
        g.edges
            .iter()
            .find(|e| e.from == "artifact:verifier_bytecode" && e.kind == "implements")
    }

    #[test]
    fn interp_route_impl_edge_is_checked_only_with_a_valid_certificate() {
        let d = Digest::of_bytes(b"image");
        let ok = graph(true, Some(d.clone()));
        let e = impl_edge(&ok).expect("implements edge");
        assert_eq!(e.status, EdgeStatus::Checked);
        assert_eq!(e.evidence, vec![d.clone()]);
        assert!(ok.edges.iter().any(|e| e.kind == "executed_by" && e.status == EdgeStatus::Tested));
        assert_eq!(impl_edge(&graph(false, Some(d))).unwrap().status, EdgeStatus::Missing);
        assert!(impl_edge(&graph(true, None)).is_none());
    }
}
