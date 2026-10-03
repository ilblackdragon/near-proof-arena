//! Findings: the internal currency between pipeline stages and gate assembly.

use arena_types::ReasonCode;
use serde::Serialize;

/// Which gates a finding affects.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Scope {
    /// Every formal gate and the axiom audit.
    All,
    /// The certificate as a whole (all FORMAL_* gates); the axiom audit only
    /// if the code is an axiom code.
    Certificate,
    /// One conjunct (index into `conjunct_gates`) plus AXIOM_AUDIT.
    Conjunct(usize),
    /// Only the ARTIFACT_BINDING gate (e.g. a candidate-supplied binary that
    /// is not the judge build; the formal proof itself is unaffected).
    Binding,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum Severity {
    /// Definite rejection.
    Fail,
    /// Could not decide (timeout, infra, missing rechecker) — never PASS.
    Unknown,
}

#[derive(Clone, Debug, Serialize)]
pub struct Finding {
    pub code: ReasonCode,
    pub scope: Scope,
    pub severity: Severity,
    pub detail: String,
}

impl Finding {
    pub fn new(code: ReasonCode, scope: Scope, detail: String) -> Self {
        Finding {
            code,
            scope,
            severity: Severity::Fail,
            detail: bound(detail),
        }
    }
    pub fn unknown(code: ReasonCode, detail: String) -> Self {
        Finding {
            code,
            scope: Scope::All,
            severity: Severity::Unknown,
            detail: bound(detail),
        }
    }
}

pub fn is_axiom_code(c: ReasonCode) -> bool {
    matches!(
        c,
        ReasonCode::ForbiddenAxiom
            | ReasonCode::SorryFound
            | ReasonCode::NativeEvalFound
            | ReasonCode::UnapprovedAssumption
    )
}

/// Bounded, plain-text (no control chars except newline) summary text.
pub fn bound(s: String) -> String {
    let mut out: String = s
        .chars()
        .map(|c| if c.is_control() && c != '\n' { ' ' } else { c })
        .take(2000)
        .collect();
    if s.chars().count() > 2000 {
        out.push('…');
    }
    out
}

pub fn lossy_tail(b: &[u8], n: usize) -> String {
    let s = String::from_utf8_lossy(b);
    let start = s.len().saturating_sub(n);
    let mut i = start;
    while !s.is_char_boundary(i) {
        i += 1;
    }
    s[i..].to_string()
}
