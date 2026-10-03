//! End-to-end tests on the public fixtures (`oracle/fixtures/public`).
use std::path::PathBuf;

fn case(name: &str) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let d = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../oracle/fixtures/public/cases").join(name);
    (
        std::fs::read(d.join("request.bin")).unwrap(),
        std::fs::read(d.join("witness.bin")).unwrap(),
        std::fs::read(d.join("expected_claim.bin")).unwrap(),
    )
}

#[test]
fn sha_column_layout_matches_plonky3() {
    use p3_sha256_air::{NUM_SHA256_COLS, Sha256Cols};
    use std::borrow::Borrow;
    let idx: Vec<usize> = (0..NUM_SHA256_COLS).collect();
    let cols: &Sha256Cols<usize> = idx[..].borrow();
    for w in [0, 13, 14, 15] {
        for t in [0, 7, 27, 31] {
            assert_eq!(cols.w[w][t], npstark::air::sha::w_bit_col(w, t));
        }
    }
}

#[test]
fn prove_verify_and_claims_match_oracle() {
    for name in ["example-tierA", "example-tierB"] {
        let (req, wit, expected) = case(name);
        let (claim, proof, _) = npstark::proof::prove(&req, &wit, true).expect("prove");
        assert_eq!(claim, expected, "{name}: claim differs from the oracle");
        npstark::proof::verify(&claim, &proof).expect("honest proof must verify");
        // a different claim with the same proof is rejected
        let mut bad = claim.clone();
        let last = bad.len() - 1;
        bad[last] ^= 1;
        assert!(npstark::proof::verify(&bad, &proof).is_err());
        // a corrupted proof is rejected
        let mut badp = proof.clone();
        let mid = badp.len() / 2;
        badp[mid] ^= 0x10;
        assert!(npstark::proof::verify(&claim, &badp).is_err());
    }
}

#[test]
fn air_digest_is_deterministic() {
    assert_eq!(npstark::proof::air_config_digest(), npstark::proof::air_config_digest());
}
