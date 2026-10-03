//! `dump-mutants`: generate the hostile proof mutants for a synthetic honest
//! proof and print their classification + explain-evidence. Useful for eyeballing
//! coverage and for the integrator to see what the ADVERSARIAL_PROOFS gate will
//! feed a verifier. Not a correctness test (that lives in tests/).

use proof_mutators::hints::{FormatHints, LenField, Region};
use proof_mutators::{generate_all, MutationCtx};

fn main() {
    // A synthetic "witness-like" honest proof: a u32 length prefix, then four
    // 32-byte words standing in for trie nodes / commitments.
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
            len: 32,
        }],
        domain_tag: Some(Region {
            label: "ctx".into(),
            offset: 4,
            len: 8,
        }),
    };
    let foreign_claim = b"claim-for-another-case".to_vec();
    let foreign_proof = b"a-genuine-proof-from-another-challenge-0123456789".to_vec();
    let ctx = MutationCtx {
        hints,
        foreign_claim: Some(&foreign_claim),
        foreign_proof: Some(&foreign_proof),
        claimed_formal_digest: None,
    };

    let claim = b"honest-claim".to_vec();
    let mutants = generate_all(&honest, &claim, &ctx, 0xC0FFEE);
    println!(
        "# {} mutants from a {}-byte honest proof",
        mutants.len(),
        honest.len()
    );
    for m in &mutants {
        println!(
            "{:22} {:28} kill={:?} bytes={} claim_override={} :: {}",
            m.mutator,
            m.label,
            m.kill,
            m.bytes.len(),
            m.claim_override.is_some(),
            m.explain,
        );
    }
}
