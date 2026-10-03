//! Byte-identity against the oracle's expected claims on every public fixture,
//! and rejection of every out-of-domain rejection fixture.
use std::path::PathBuf;

fn fixtures() -> PathBuf {
    let p = std::env::var("NEARPROOF_FIXTURES").map(PathBuf::from).unwrap_or_else(|_| {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../../oracle/fixtures")
    });
    p
}

#[test]
fn public_fixtures_match_expected_claim() {
    let dir = fixtures().join("public/cases");
    let mut n = 0;
    for e in std::fs::read_dir(&dir).unwrap() {
        let d = e.unwrap().path();
        let req = std::fs::read(d.join("request.bin")).unwrap();
        let wit = std::fs::read(d.join("witness.bin")).unwrap();
        let want = std::fs::read(d.join("expected_claim.bin")).unwrap();
        let (got, _) = transfer_core::derive_claim(&req, &wit).unwrap_or_else(|e| panic!("{d:?}: {e:?}"));
        assert_eq!(got, want, "{d:?}");
        assert!(transfer_core::claim_well_formed(&got));
        n += 1;
    }
    assert!(n >= 20);
}

#[test]
fn rejection_fixtures_refused() {
    let dir = fixtures().join("rejection/cases");
    let mut n = 0;
    for e in std::fs::read_dir(&dir).unwrap() {
        let d = e.unwrap().path();
        let req = std::fs::read(d.join("request.bin")).unwrap();
        let wit = std::fs::read(d.join("witness.bin")).unwrap_or_default();
        let r = transfer_core::derive_claim(&req, &wit);
        assert!(r.is_err(), "{d:?} accepted");
        n += 1;
    }
    assert!(n >= 14);
}

#[test]
fn params_match_fixture() {
    let p = std::fs::read(fixtures().join("public/params.bin")).unwrap();
    assert_eq!(p, transfer_core::expected_params());
}

#[test]
fn tampered_witness_rejected() {
    let d = fixtures().join("public/cases/s20261003-v0");
    let req = std::fs::read(d.join("request.bin")).unwrap();
    let wit = std::fs::read(d.join("witness.bin")).unwrap();
    // flip every 97th byte after the header: must never yield the expected claim
    let want = std::fs::read(d.join("expected_claim.bin")).unwrap();
    for i in (70..wit.len()).step_by(97) {
        let mut w = wit.clone();
        w[i] ^= 1;
        if let Ok((c, _)) = transfer_core::derive_claim(&req, &w) {
            assert_ne!(c, want, "byte {i}");
        }
    }
}
