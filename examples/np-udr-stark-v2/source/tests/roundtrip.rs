use npudr::field::F;
use npudr::prover::{ProveOptions, prove_bytes};
use npudr::toy;
use npudr::verifier::verify;

const PUB: &[u8] = b"public tape";
const O: ProveOptions = ProveOptions { verbose: false };

#[test]
fn fib_roundtrip() {
    for log_n in [4usize, 5, 8, 10] {
        let air = toy::fib_air();
        let (tr, last) = toy::fib_trace(log_n, 1, 1);
        let cb = toy::fib_claim(1, 1, last);
        let b = prove_bytes(&air, vec![tr], PUB, &cb, &O).unwrap();
        verify(&air, PUB, &cb, &b).unwrap_or_else(|e| panic!("log_n={log_n}: {e}"));
        let bad = toy::fib_claim(1, 1, last + F::new(1));
        assert!(verify(&air, PUB, &bad, &b).is_err());
    }
}

#[test]
fn fib_bad_trace_rejected_by_prover() {
    let air = toy::fib_air();
    let (tr, last) = toy::fib_trace(6, 1, 1);
    let cb = toy::fib_claim(1, 1, last + F::new(1));
    assert!(prove_bytes(&air, vec![tr], PUB, &cb, &O).is_err());
}

#[test]
fn multi_roundtrip() {
    let air = toy::multi_air();
    for (lf, lc) in [(6usize, 3usize), (3, 7), (10, 10), (9, 1)] {
        let (tr, last) = toy::fib_trace(lf, 1, 1);
        let cb = toy::fib_claim(1, 1, last);
        let traces = vec![tr, toy::cube_trace(3, lc), toy::cube_trace(1, 1)];
        let b = prove_bytes(&air, traces, PUB, &cb, &O).unwrap();
        verify(&air, PUB, &cb, &b).unwrap_or_else(|e| panic!("({lf},{lc}): {e}"));
    }
}

#[test]
fn bus_roundtrip() {
    let air = toy::bus_air();
    let xs: Vec<u32> = (0..32u32).map(|i| (i * 7) % 13).collect();
    for (lr, lu) in [(4usize, 5usize), (6, 5), (5, 8)] {
        let b = prove_bytes(&air, toy::bus_traces(lr, lu, &xs), PUB, &[], &O).unwrap();
        verify(&air, PUB, &[], &b).unwrap_or_else(|e| panic!("({lr},{lu}): {e}"));
    }
}

#[test]
fn bus_unbalanced_rejected_by_prover() {
    let air = toy::bus_air();
    let xs: Vec<u32> = (0..32u32).map(|i| (i * 7) % 13).collect();
    let mut tr = toy::bus_traces(4, 5, &xs);
    // claim one more use of value 3 than actually looked up
    let v = 3;
    let c = tr[0].values[5 * v + 1];
    tr[0].values[5 * v + 1] = F::new(1) - c;
    assert!(prove_bytes(&air, tr, PUB, &[], &O).is_err());
}

#[test]
fn small_query_domain_rejected() {
    // minQueryLog = 8: the largest table needs >= 16 rows
    let air = toy::fib_air();
    for log_n in [1usize, 2, 3] {
        let (tr, last) = toy::fib_trace(log_n, 1, 1);
        let cb = toy::fib_claim(1, 1, last);
        let e = prove_bytes(&air, vec![tr], PUB, &cb, &O).unwrap_err();
        assert!(e.contains("pad"), "{e}");
    }
    // a valid proof whose header is rewritten to a smaller height is rejected
    let (tr, last) = toy::fib_trace(4, 1, 1);
    let cb = toy::fib_claim(1, 1, last);
    let mut b = prove_bytes(&air, vec![tr], PUB, &cb, &O).unwrap();
    b[8] = 3;
    assert!(verify(&air, PUB, &cb, &b).is_err());
}
