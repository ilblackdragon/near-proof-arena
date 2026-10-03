//! Unit tests for the hostile proof mutators: every mutant must differ from the
//! honest proof (or be an explicit substitution), carry a correct kill class,
//! and the generators must be deterministic and panic-free on odd inputs.

use proof_mutators::hints::{FormatHints, LenField, Region};
use proof_mutators::{generate_all, KillKind, MutationCtx};

fn synthetic() -> (Vec<u8>, FormatHints) {
    let mut honest = Vec::new();
    honest.extend_from_slice(&128u32.to_le_bytes());
    for w in 0u8..4 {
        honest.extend(std::iter::repeat_n(w.wrapping_add(1), 32));
    }
    let hints = FormatHints {
        commitments: vec![Region {
            label: "root".into(),
            offset: 4,
            len: 32,
        }],
        lengths: vec![LenField {
            label: "witness_len".into(),
            offset: 0,
            width: 4,
        }],
        trie_nodes: vec![
            Region {
                label: "n0".into(),
                offset: 4,
                len: 32,
            },
            Region {
                label: "n1".into(),
                offset: 36,
                len: 32,
            },
            Region {
                label: "n2".into(),
                offset: 68,
                len: 32,
            },
        ],
        transcript: vec![Region {
            label: "fs".into(),
            offset: 100,
            len: 28,
        }],
        domain_tag: Some(Region {
            label: "ctx".into(),
            offset: 4,
            len: 8,
        }),
    };
    (honest, hints)
}

fn full_ctx<'a>(hints: FormatHints, fc: &'a [u8], fp: &'a [u8]) -> MutationCtx<'a> {
    MutationCtx {
        hints,
        foreign_claim: Some(fc),
        foreign_proof: Some(fp),
        claimed_formal_digest: None,
    }
}

#[test]
fn every_mutant_is_hostile_and_differs() {
    let (honest, hints) = synthetic();
    let fc = b"foreign-claim".to_vec();
    let fp = b"foreign-proof-from-another-challenge-aaaaaaaaaaaa".to_vec();
    let ctx = full_ctx(hints, &fc, &fp);
    let claim = b"claim".to_vec();
    let mutants = generate_all(&honest, &claim, &ctx, 1);
    assert!(
        mutants.len() >= 20,
        "expected a broad mutant set, got {}",
        mutants.len()
    );

    for m in &mutants {
        // Each mutant either changes the proof bytes, or is an explicit
        // substitution (foreign proof) / context change (foreign claim).
        let changed_bytes = m.bytes != honest;
        let substitution = m.mutator == "recursive-substitution";
        let context_only = m.claim_override.is_some();
        assert!(
            changed_bytes || substitution || context_only,
            "mutant {}/{} neither changed bytes nor substituted context",
            m.mutator,
            m.label
        );
        assert!(
            !m.explain.is_empty(),
            "{}/{} missing explain",
            m.mutator,
            m.label
        );
        // labels unique per (mutator,label)
    }

    // No duplicate (mutator,label) keys.
    let mut keys: Vec<(String, String)> = mutants
        .iter()
        .map(|m| (m.mutator.clone(), m.label.clone()))
        .collect();
    keys.sort();
    let before = keys.len();
    keys.dedup();
    assert_eq!(before, keys.len(), "duplicate mutant labels");
}

#[test]
fn classification_is_present_and_sane() {
    let (honest, hints) = synthetic();
    let fc = b"foreign-claim".to_vec();
    let fp = b"foreign-proof-xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx".to_vec();
    let ctx = full_ctx(hints, &fc, &fp);
    let mutants = generate_all(&honest, b"claim", &ctx, 2);

    // Binding kills exist (mismatched context, recursive substitution, domain).
    assert!(mutants.iter().any(|m| m.kill == KillKind::Binding));
    // Semantic kills exist (commitment flip, siblings, node-type).
    assert!(mutants.iter().any(|m| m.kill == KillKind::Semantic));
    // Packaging kills exist (truncate, empty, lengths).
    assert!(mutants.iter().any(|m| m.kill == KillKind::Packaging));

    // A stale-digest style failure would be Packaging, NOT Semantic — asserted
    // here as documentation of the invariant: the altered-commitment flip is
    // the semantic one, truncation/length are packaging.
    let altered: Vec<_> = mutants
        .iter()
        .filter(|m| m.mutator == "altered-commitment")
        .collect();
    assert!(!altered.is_empty());
    assert!(altered.iter().all(|m| m.kill == KillKind::Semantic));
    let trunc: Vec<_> = mutants.iter().filter(|m| m.mutator == "truncate").collect();
    assert!(trunc.iter().all(|m| m.kill == KillKind::Packaging));
}

#[test]
fn deterministic_given_seed() {
    let (honest, hints) = synthetic();
    let fc = b"fc".to_vec();
    let fp = b"fp-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_vec();
    let ctx = full_ctx(hints, &fc, &fp);
    let a = generate_all(&honest, b"claim", &ctx, 99);
    let b = generate_all(&honest, b"claim", &ctx, 99);
    assert_eq!(a.len(), b.len());
    for (x, y) in a.iter().zip(b.iter()) {
        assert_eq!(x.bytes, y.bytes);
        assert_eq!(x.label, y.label);
        assert_eq!(x.kill, y.kill);
    }
}

#[test]
fn no_hints_falls_back_to_inference() {
    // Opaque proof, empty hints: inference should still yield mutants.
    let honest: Vec<u8> = (0..160u16).map(|i| (i % 256) as u8).collect();
    let ctx = MutationCtx::default();
    let mutants = generate_all(&honest, b"claim", &ctx, 3);
    assert!(
        mutants.len() >= 8,
        "inference should still produce a useful set, got {}",
        mutants.len()
    );
    // Commitment/length mutants should appear via inference.
    assert!(mutants.iter().any(|m| m.mutator == "altered-commitment"));
}

#[test]
fn panic_free_on_degenerate_inputs() {
    let ctx = MutationCtx::default();
    for honest in [
        vec![],
        vec![0u8],
        vec![1u8, 2],
        (0..3u8).collect::<Vec<_>>(),
    ] {
        let _ = generate_all(&honest, b"", &ctx, 4);
        let _ = generate_all(&honest, b"claim", &ctx, 5);
    }
}

#[test]
fn foreign_artifacts_required_for_binding_subst() {
    // Without foreign proof/claim, those mutators produce nothing (not a pass).
    let (honest, hints) = synthetic();
    let ctx = MutationCtx {
        hints,
        ..Default::default()
    };
    let mutants = generate_all(&honest, b"claim", &ctx, 6);
    assert!(mutants
        .iter()
        .all(|m| m.mutator != "recursive-substitution"));
    assert!(mutants.iter().all(|m| m.mutator != "mismatched-context"));
    // but structural mutators still fire
    assert!(mutants.iter().any(|m| m.mutator == "swapped-siblings"));
}

#[test]
fn nested_trie_node_hints_do_not_panic() {
    use proof_mutators::hints::{FormatHints, Region};
    use proof_mutators::{generate_all, MutationCtx};
    let honest: Vec<u8> = (0..200u8).collect();
    let hints = FormatHints {
        trie_nodes: vec![
            Region {
                label: "child".into(),
                offset: 50,
                len: 20,
            },
            Region {
                label: "parent".into(),
                offset: 40,
                len: 60,
            },
        ],
        ..FormatHints::default()
    };
    let ctx = MutationCtx {
        hints,
        ..MutationCtx::default()
    };
    let _ = generate_all(&honest, b"claim", &ctx, 7);
}
