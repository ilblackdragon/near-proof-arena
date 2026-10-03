//! NEAR Proof Arena formal checker.
//!
//! Decides the formal gates (`FORMAL_*`, `AXIOM_AUDIT`) for a candidate Lean
//! project whose certificate constant must have *exactly* the judge-constructed
//! admission statement as its type. See `README.md` for the threat model.

pub mod audit;
pub mod digest;
pub mod expected;
pub mod findings;
pub mod grep;
pub mod ndjson;
pub mod pipeline;
pub mod report;
pub mod sandbox;
pub mod staging;
pub mod toolchain;

pub use expected::{ExpectedTypeBuilder, LeanValue, TemplateExpected};
pub use pipeline::{CheckRequest, FormalChecker, Limits, Policy, TrustedPackage};
pub use report::FormalCheckReport;
pub use sandbox::{BwrapDevRunner, UntrustedRunner};
