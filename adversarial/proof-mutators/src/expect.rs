//! Typed loader for `expect.json`, the expected-outcome contract that ships
//! with every hostile submission. The e2e driver asserts the server's actual
//! decision / gates / reason codes against this file.

use arena_types::{Decision, ObligationId, ReasonCode, Stage};
use serde::{Deserialize, Serialize};

fn default_targets() -> Vec<String> {
    vec!["demo".to_string()]
}
fn default_runnable() -> bool {
    true
}

/// Expected judge outcome for one hostile submission.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Expect {
    /// Case directory name (must match the folder).
    pub case: String,
    /// Attack family, for grouping in the report.
    pub attack_family: String,
    /// Which challenge kind(s) this case is meaningful on: `"demo"` and/or
    /// `"near-formal"`, or `"near-v3"` (the v3 chunk-validation challenges). A gate only exists where the challenge requires it, so
    /// formal/artifact/crypto cases are `["near-formal"]` and the demo run
    /// skips them (and vice-versa). Defaults to `["demo"]`.
    #[serde(default = "default_targets")]
    pub targets: Vec<String>,
    /// Whether the e2e driver should actually submit this case. `false` for the
    /// generic Lean-certificate stubs, which document an attack but need a real
    /// reexec-witness backend to execute (the executable NEAR kills are the
    /// `near-reexec-*` cases). Defaults to `true`.
    #[serde(default = "default_runnable")]
    pub runnable: bool,
    /// The decision the judge must reach. For every hostile case this is
    /// `REJECTED` (or `INCONCLUSIVE` only where noted), never `ADMITTED`.
    pub expected_decision: Decision,
    /// At least one of these gates must FAIL (order-independent). Empty is only
    /// valid when `expected_decision` is `INCONCLUSIVE`.
    pub expected_failing_gates: Vec<ObligationId>,
    /// Reason codes that must appear among the failing gates' `reason_codes`.
    pub expected_reason_codes: Vec<ReasonCode>,
    /// Earliest stage at which the failure is expected (for fail-fast checks).
    /// The judge may fail earlier; the driver only requires failure no later.
    pub fail_by_stage: Option<Stage>,
    /// Outcomes that must NEVER occur for this submission, as strings
    /// (`"ADMITTED"`, `"ranked"`, `"accepted"`). Always includes `ADMITTED`.
    pub must_never: Vec<String>,
    /// Why this is hostile and what the kill proves about the judge.
    pub why: String,
    /// Optional free-form notes (build-image assumptions, caveats).
    #[serde(default)]
    pub notes: Option<String>,
}

#[derive(Debug, thiserror::Error)]
pub enum ExpectError {
    #[error("io: {0}")]
    Io(#[from] std::io::Error),
    #[error("json: {0}")]
    Json(#[from] serde_json::Error),
    #[error("invalid expect.json for {case}: {msg}")]
    Invalid { case: String, msg: String },
}

impl Expect {
    pub fn parse(s: &str) -> Result<Self, ExpectError> {
        let e: Expect = serde_json::from_str(s)?;
        e.validate()?;
        Ok(e)
    }

    pub fn validate(&self) -> Result<(), ExpectError> {
        let bad = |msg: &str| {
            Err(ExpectError::Invalid {
                case: self.case.clone(),
                msg: msg.to_string(),
            })
        };
        // No hostile case may ever be admitted.
        if self.expected_decision == Decision::Admitted {
            return bad("a hostile case must never expect ADMITTED");
        }
        if !self.must_never.iter().any(|s| s == "ADMITTED") {
            return bad("must_never must list ADMITTED");
        }
        match self.expected_decision {
            Decision::Rejected => {
                if self.expected_failing_gates.is_empty() {
                    return bad("REJECTED requires at least one expected failing gate");
                }
                if self.expected_reason_codes.is_empty() {
                    return bad("REJECTED requires at least one expected reason code");
                }
            }
            Decision::Inconclusive => {} // may have empty gates (UNKNOWN mandatory)
            _ => return bad("expected_decision must be REJECTED or INCONCLUSIVE"),
        }
        if self.targets.is_empty() {
            return bad("targets must be non-empty");
        }
        if let Some(t) = self
            .targets
            .iter()
            .find(|t| !matches!(t.as_str(), "demo" | "near-formal" | "near-v3"))
        {
            return bad(&format!(
                "unknown target {t:?} (expected demo | near-formal | near-v3)"
            ));
        }
        Ok(())
    }
}
