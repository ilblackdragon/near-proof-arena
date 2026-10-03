//! GateResult construction helpers.

use arena_types::{EvidenceRef, GateResult, GateStatus, ObligationId, ReasonCode};
use time::format_description::well_known::Rfc3339;

pub fn now() -> String {
    time::OffsetDateTime::now_utc()
        .format(&Rfc3339)
        .unwrap_or_default()
}

/// Plain text, no control characters except newline, at most 2000 chars.
pub fn sanitize(s: &str) -> String {
    let mut out: String = s
        .chars()
        .filter(|c| *c == '\n' || !c.is_control())
        .take(2000)
        .collect();
    if s.chars().count() > 2000 {
        out.push('…');
    }
    out
}

/// Accumulates the outcome of one gate.
#[derive(Clone, Debug)]
pub struct Gate {
    pub gate: ObligationId,
    pub started_at: String,
    pub status: Option<GateStatus>,
    pub reasons: Vec<ReasonCode>,
    pub notes: Vec<String>,
    pub evidence: Vec<EvidenceRef>,
}

impl Gate {
    pub fn start(gate: ObligationId) -> Self {
        Gate {
            gate,
            started_at: now(),
            status: None,
            reasons: vec![],
            notes: vec![],
            evidence: vec![],
        }
    }
    /// Record a failure (FAIL dominates everything).
    pub fn fail(&mut self, reason: ReasonCode, note: impl Into<String>) {
        self.status = Some(GateStatus::Fail);
        if !self.reasons.contains(&reason) {
            self.reasons.push(reason);
        }
        self.notes.push(note.into());
    }
    pub fn failed(&self) -> bool {
        self.status == Some(GateStatus::Fail)
    }
    pub fn note(&mut self, note: impl Into<String>) {
        self.notes.push(note.into());
    }
    pub fn evidence(
        &mut self,
        label: impl Into<String>,
        digest: arena_types::Digest,
        public: bool,
    ) {
        self.evidence.push(EvidenceRef {
            label: label.into(),
            digest,
            public,
        });
    }
    /// Finish: unless failed, the gate is `if_not_failed` (PASS when the
    /// check ran to completion, UNKNOWN when it was cut short).
    pub fn finish(self, if_not_failed: GateStatus, mandatory: bool) -> GateResult {
        let status = self.status.unwrap_or(if_not_failed);
        GateResult {
            gate: self.gate,
            mandatory,
            status,
            reason_codes: self.reasons,
            summary: sanitize(&self.notes.join("; ")),
            evidence: self.evidence,
            started_at: Some(self.started_at),
            finished_at: Some(now()),
            reused_from: None,
        }
    }
}
