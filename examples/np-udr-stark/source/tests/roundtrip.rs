use npudr::field::F;
use npudr::protocol::Proof;
use npudr::prover::{prove, ProveOptions};
use npudr::toy;
use npudr::verifier::verify;

const PD: [u8; 32] = [7u8; 32];

#[test]
fn fib_roundtrip() {
    for log_n in [2usize, 3, 5, 8, 10] {
        let air = toy::fib_air();
        let (tr, last) = toy::fib_trace(log_n, 1, 1);
        let cb = toy::fib_claim(1, 1, last);
        let p = prove(&air, &[tr], &PD, &cb, &ProveOptions { verbose: false }).unwrap();
        let b = p.to_bytes();
        assert_eq!(Proof::from_bytes(&b).unwrap(), p);
        verify(&air, &PD, &cb, &b).unwrap_or_else(|e| panic!("log_n={log_n}: {e}"));
        // wrong claim must fail
        let bad = toy::fib_claim(1, 1, last + F::new(1));
        assert!(verify(&air, &PD, &bad, &b).is_err());
    }
}

#[test]
fn fib_bad_trace_rejected_by_prover() {
    let air = toy::fib_air();
    let (tr, last) = toy::fib_trace(6, 1, 1);
    let cb = toy::fib_claim(1, 1, last + F::new(1));
    assert!(prove(&air, &[tr], &PD, &cb, &ProveOptions { verbose: false }).is_err());
}

#[test]
fn multi_roundtrip() {
    let air = toy::multi_air();
    for (lf, lc) in [(6usize, 3usize), (3, 7), (10, 10), (9, 1)] {
        let (tr, last) = toy::fib_trace(lf, 1, 1);
        let cb = toy::fib_claim(1, 1, last);
        let traces = vec![tr, toy::cube_trace(3, lc), toy::cube_trace(1, 1)];
        let p = prove(&air, &traces, &PD, &cb, &ProveOptions { verbose: false }).unwrap();
        let b = p.to_bytes();
        verify(&air, &PD, &cb, &b).unwrap_or_else(|e| panic!("({lf},{lc}): {e}"));
    }
}
