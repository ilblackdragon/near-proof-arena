//! `np-udr-stark-v2`: public segments and `auxGroup ∈ {1,2,3}` (FORMATS.md §8).

use npudr::air::Air;
use npudr::prover::{ProveOptions, prove_bytes};
use npudr::toy;
use npudr::verifier::{pub_fit, verify};

const PUB: &[u8] = b"public tape";
const O: ProveOptions = ProveOptions { verbose: false };

fn case() -> (Vec<(u8, u8)>, Vec<u8>, Vec<u32>) {
    let recs: Vec<(u8, u8)> = (0..11u8).map(|j| (j.wrapping_mul(37), 255 - j)).collect();
    let vals: Vec<u8> = (0..5u8).map(|j| j * 51).collect();
    (recs, vals, vec![1, 3, 3, 7, 0, 15])
}

fn prove(
    g: usize,
    recs: &[(u8, u8)],
    vals: &[u8],
    xs: &[u32],
    gap: usize,
) -> (Air, Vec<u8>, Vec<u8>) {
    let air = toy::pubseg_air(g);
    air.validate().unwrap();
    let cb = toy::pubseg_claim(recs, vals, gap);
    let tr = toy::pubseg_traces(4, 4, xs, 4, recs, 3, vals);
    let b = prove_bytes(&air, tr, PUB, &cb, &O).unwrap_or_else(|e| panic!("g={g}: {e}"));
    (air, cb, b)
}

#[test]
fn json_roundtrip_v2() {
    for g in 1..=3 {
        let air = toy::pubseg_air(g);
        let j = air.to_json();
        assert!(j.starts_with("{\"format\":\"np-air-v2\""));
        let back = Air::from_json(&j).unwrap();
        assert_eq!(back.pub_segs, air.pub_segs);
        assert_eq!(back.max_pub, air.max_pub);
        assert_eq!(back.to_json(), j);
    }
}

#[test]
fn layout_depends_on_group() {
    let a1 = toy::pubseg_air(1);
    let pin = &a1.tables[3];
    // pin: 2 sends, 3 receives (1-bit each): finals 2+3 / 1+2 / 1+1
    assert_eq!(pin.num_finals(1), 5);
    assert_eq!(pin.num_finals(2), 3);
    assert_eq!(pin.num_finals(3), 2);
    // group degree 2 + Σ phiDegree (each 1 + 1 = 2)
    assert_eq!(pin.degree(1), 4);
    assert_eq!(pin.degree(2), 6);
    assert_eq!(pin.degree(3), 8);
}

#[test]
fn pubseg_roundtrip_all_groups() {
    let (recs, vals, xs) = case();
    for g in 1..=3 {
        for gap in [0usize, 5] {
            let (air, cb, b) = prove(g, &recs, &vals, &xs, gap);
            verify(&air, PUB, &cb, &b).unwrap_or_else(|e| panic!("g={g} gap={gap}: {e}"));
            // the proof does not transfer to another group size
            for h in (1..=3).filter(|&h| h != g) {
                let other = toy::pubseg_air(h);
                assert!(
                    verify(&other, PUB, &cb, &b).is_err(),
                    "g={g}: proof accepted under auxGroup {h}"
                );
            }
        }
    }
}

#[test]
fn pubseg_wrong_claims_rejected() {
    let (recs, vals, xs) = case();
    let (air, cb, b) = prove(2, &recs, &vals, &xs, 3);
    // a changed seg-0 payload byte, seg-1 payload byte, and a pad byte (pad is unread)
    let mut c = cb.clone();
    c[12 + 4] ^= 1;
    assert!(verify(&air, PUB, &c, &b).is_err());
    let mut c = cb.clone();
    let last = c.len() - 1;
    c[last] ^= 1;
    assert!(verify(&air, PUB, &c, &b).is_err());
    // count past the claim → pubFit fails (the full verifier may already reject at
    // parse, since the claim is absorbed into the transcript; either way it rejects)
    let mut c = cb.clone();
    c[0..4].copy_from_slice(&1000u32.to_le_bytes());
    assert!(!pub_fit(&air, &c));
    assert!(verify(&air, PUB, &c, &b).is_err());
    // maxPub below the used extent: same claim and transcript, rejected by pubFit
    let mut small = air.clone();
    small.max_pub = cb.len() - 1;
    assert!(pub_fit(&air, &cb) && !pub_fit(&small, &cb));
    let e = verify(&small, PUB, &cb, &b).unwrap_err();
    assert!(e.contains("pubFit"), "{e}");
    // a hostile count of 2^32-1 is rejected by pubFit without enumerating records
    let mut c = cb.clone();
    c[8..12].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(!pub_fit(&air, &c));
    assert!(verify(&air, PUB, &c, &b).is_err());
    // a payload offset (startAt) past the claim
    let mut c = cb.clone();
    c[4..8].copy_from_slice(&(cb.len() as u32).to_le_bytes());
    assert!(!pub_fit(&air, &c));
}

#[test]
fn prover_refuses_unbalanced_claim() {
    let (recs, vals, xs) = case();
    let air = toy::pubseg_air(2);
    let tr = toy::pubseg_traces(4, 4, &xs, 4, &recs, 3, &vals);
    let mut cb = toy::pubseg_claim(&recs, &vals, 0);
    cb[13] ^= 1; // a seg-0 record the trace does not receive
    assert!(prove_bytes(&air, tr, PUB, &cb, &O).is_err());
}
