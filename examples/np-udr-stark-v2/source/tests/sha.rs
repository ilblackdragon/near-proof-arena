//! SHA-256 toy (src/sha.rs): honest traces satisfy every constraint and
//! balance both buses; proofs round-trip through the reference verifier;
//! tampering is caught by the prover / verifier.
use npudr::air::Air;
use npudr::check::{bus_imbalance, failing_constraints};
use npudr::field::F;
use npudr::prover::{ProveOptions, prove_bytes};
use npudr::sha;
use npudr::verifier::verify;

const PUB: &[u8] = b"sha toy";
const O: ProveOptions = ProveOptions { verbose: false };

fn assert_honest(lens: &[usize]) {
    let msgs = sha::toy_msgs(lens);
    let air = sha::sha_air();
    let trs = sha::sha_traces(&msgs);
    for (t, tr) in air.tables.iter().zip(&trs) {
        let bad = failing_constraints(t, tr, &[], 10);
        assert!(bad.is_empty(), "{lens:?}: table {} fails {bad:?}", t.name);
    }
    let im = bus_imbalance(&air, &trs, &[]);
    assert!(
        im.is_empty(),
        "{lens:?}: bus imbalance {:?}",
        &im[..im.len().min(3)]
    );
}

#[test]
fn honest_traces_satisfy_air() {
    for lens in [
        &[0usize][..],
        &[55],
        &[56],
        &[64],
        &[119],
        &[951],
        &[1000],
        &[0, 55, 56, 64, 119, 1000, 3],
    ] {
        assert_honest(lens);
    }
}

#[test]
fn air_json_roundtrip_and_shape() {
    let air = sha::sha_air();
    air.validate().unwrap();
    let j = air.to_json();
    assert_eq!(Air::from_json(&j).unwrap().to_json(), j);
    assert_eq!(air.tables[0].width, 544);
    assert_eq!(air.tables[0].constraints.len(), 1011 + 17);
    assert_eq!(air.tables[0].degree(1), 4);
}

#[test]
fn sha_prove_verify_and_reject() {
    let msgs = sha::toy_msgs(&[0, 3, 56, 119]);
    let air = sha::sha_air();
    let b = prove_bytes(&air, sha::sha_traces(&msgs), PUB, &[], &O).unwrap();
    verify(&air, PUB, &[], &b).unwrap();
    for off in [0, 9, 100, b.len() / 3, b.len() / 2, b.len() - 1] {
        let mut m = b.clone();
        m[off] ^= 1;
        assert!(verify(&air, PUB, &[], &m).is_err(), "flip@{off} accepted");
    }
    assert!(verify(&air, PUB, &[], &b[..b.len() - 1]).is_err());
    assert!(verify(&air, b"other", &[], &b).is_err());
}

#[test]
fn tampered_traces_rejected_by_prover() {
    let msgs = sha::toy_msgs(&[5, 70]);
    let air = sha::sha_air();
    // a wrong digest byte in the consumer: constraints hold, bus does not
    let mut trs = sha::sha_traces(&msgs);
    trs[2].values[35 + 2 + 7] += F::new(1);
    assert_eq!(bus_imbalance(&air, &trs, &[]).len(), 2);
    assert!(prove_bytes(&air, trs, PUB, &[], &O).is_err());
    // a flipped `a` bit on round row R2 of the first block (row 3)
    let mut trs = sha::sha_traces(&msgs);
    let cell = 3 * sha::WIDTH + sha::col_a(1, 5);
    trs[0].values[cell] = F::new(1) - trs[0].values[cell];
    let bad = failing_constraints(&air.tables[0], &trs[0], &[], 100);
    assert!(!bad.is_empty());
    assert!(prove_bytes(&air, trs, PUB, &[], &O).is_err());
}
