//! Proof-mutator tests: every single-bit flip, truncation or extension of an
//! honest proof must be rejected by the reference verifier.
use npudr::air::Air;
use npudr::prover::{prove_bytes, ProveOptions};
use npudr::toy;
use npudr::verifier::verify;

const PD: &[u8] = b"pub";

fn honest() -> (Air, Vec<u8>, Vec<u8>) {
    // multi-table, mixed heights, buses
    let mut air = toy::multi_air();
    let bus = toy::bus_air();
    air.tables.extend(bus.tables);
    air.num_buses = bus.num_buses;
    let (tr, last) = toy::fib_trace(5, 2, 3);
    let cb = toy::fib_claim(2, 3, last);
    let mut traces = vec![tr, toy::cube_trace(3, 3), toy::cube_trace(1, 1)];
    let xs: Vec<u32> = (0..20u32).map(|i| (i * 5) % 11).collect();
    traces.extend(toy::bus_traces(4, 5, &xs));
    let b = prove_bytes(&air, traces, PD, &cb, &ProveOptions { verbose: false }).unwrap();
    (air, cb, b)
}

#[test]
fn bit_flips_rejected() {
    let (air, cb, b) = honest();
    verify(&air, PD, &cb, &b).unwrap();
    // deterministic xorshift sample of positions, plus every byte of the
    // first 4 KiB (header, roots, OOD values, FRI roots, final polynomial)
    let mut s: u64 = 0x9e3779b97f4a7c15;
    let mut pos: Vec<usize> = (0..b.len().min(4096)).collect();
    for _ in 0..3000 {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        pos.push((s % b.len() as u64) as usize);
    }
    for (n, &p) in pos.iter().enumerate() {
        let mut m = b.clone();
        m[p] ^= 1 << (n % 8);
        assert!(verify(&air, PD, &cb, &m).is_err(), "bit flip at byte {p} accepted");
    }
}

#[test]
fn truncation_and_extension_rejected() {
    let (air, cb, b) = honest();
    for cut in [1usize, 4, 32, 64, b.len() / 2] {
        assert!(verify(&air, PD, &cb, &b[..b.len() - cut]).is_err());
    }
    let mut e = b.clone();
    e.push(0);
    assert!(verify(&air, PD, &cb, &e).is_err());
    assert!(verify(&air, PD, &cb, &[]).is_err());
}

#[test]
fn other_public_digest_or_claim_rejected() {
    let (air, cb, b) = honest();
    assert!(verify(&air, b"puB", &cb, &b).is_err());
    let mut cb2 = cb.clone();
    cb2.push(0);
    assert!(verify(&air, PD, &cb2, &b).is_err());
}

#[test]
fn air_json_roundtrip() {
    let air = toy::multi_air();
    let j = air.to_json();
    let a2 = Air::from_json(&j).unwrap();
    assert_eq!(a2.to_json(), j);
}
