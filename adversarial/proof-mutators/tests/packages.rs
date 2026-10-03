//! Local well-formedness tests for the hostile-submission suite. These do NOT
//! run a server; they assert the packages parse, the expectations are valid and
//! self-consistent, and no case ever expects to be admitted. The full e2e run
//! (adversarial/e2e) submits them to a live judge.

use arena_types::Decision;
use proof_mutators::suite;

#[test]
fn suite_is_well_formed() {
    let root = suite::default_root();
    let cases = suite::load_all(&root).expect("suite load");
    assert!(
        cases.len() >= 30,
        "expected a broad suite, got {}",
        cases.len()
    );

    for c in &cases {
        // The invariant that defines this lane: nothing hostile is ever admitted.
        assert_ne!(
            c.expect.expected_decision,
            Decision::Admitted,
            "{} expects ADMITTED",
            c.name
        );
        assert!(
            c.expect.must_never.iter().any(|s| s == "ADMITTED"),
            "{} must_never is missing ADMITTED",
            c.name
        );
        assert!(
            !c.expect.why.trim().is_empty(),
            "{} has no rationale",
            c.name
        );
    }
}

#[test]
fn every_attack_family_is_covered() {
    let cases = suite::load_all(&suite::default_root()).expect("suite load");
    let families: std::collections::BTreeSet<_> = cases
        .iter()
        .map(|c| c.expect.attack_family.as_str())
        .collect();
    for required in [
        "verifier-soundness",
        "prover-reliability",
        "artifact-binding",
        "public-input-binding",
        "theorem-type-mismatch",
        "axiom-audit",
        "crypto-soundness",
        "forged-output",
        "benchmark-cheat",
        "async-cheat",
        "sandbox-escape",
        "ui-log-injection",
        "build-integrity",
        "archive-attack",
    ] {
        assert!(
            families.contains(required),
            "missing attack family: {required}"
        );
    }
}

#[test]
fn expected_gates_and_reasons_are_known_contract_values() {
    // Deserializing expect.json already enforces this (the fields are typed as
    // arena_types enums), so loading the whole suite is the check.
    let cases = suite::load_all(&suite::default_root()).expect("suite load");
    for c in &cases {
        match c.expect.expected_decision {
            Decision::Rejected => {
                assert!(!c.expect.expected_failing_gates.is_empty(), "{}", c.name);
                assert!(!c.expect.expected_reason_codes.is_empty(), "{}", c.name);
            }
            Decision::Inconclusive => {}
            d => panic!("{} has unexpected decision {d:?}", c.name),
        }
    }
}
