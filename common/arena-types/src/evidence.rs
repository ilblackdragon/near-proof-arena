use crate::Digest;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum NodeKind {
    NearcoreSource,
    FormalSemantics,
    BackendSemantics,
    Theorem,
    Assumption,
    Artifact,
    TcbComponent,
    TestSuite,
    Measurement,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum EdgeStatus {
    /// Machine-checked evidence (kernel-checked proof, digest equality, ...).
    Checked,
    /// Approved, visible trusted-base entry.
    Trusted,
    /// Only tested (differential/fuzz); NOT a substitute for a formal arrow.
    Tested,
    /// No evidence. Must be rendered.
    Missing,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct EvidenceNode {
    pub id: String,
    pub kind: NodeKind,
    pub label: String,
    pub digest: Option<Digest>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct EvidenceEdge {
    pub from: String,
    pub to: String,
    /// e.g. `refines`, `binds`, `assumes`, `built_from`, `tested_against`.
    pub kind: String,
    pub status: EdgeStatus,
    pub evidence: Vec<Digest>,
    pub note: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
pub struct EvidenceGraph {
    pub nodes: Vec<EvidenceNode>,
    pub edges: Vec<EvidenceEdge>,
}

impl EvidenceGraph {
    pub fn missing_edges(&self) -> impl Iterator<Item = &EvidenceEdge> {
        self.edges
            .iter()
            .filter(|e| e.status == EdgeStatus::Missing)
    }
}
