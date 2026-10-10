//! The low-memory prover must produce exactly the reference prover's proofs.
use npudr::prover::{self, ProveOptions};
use npudr::{prover_ref, toy};

const PUB: &[u8] = b"public tape";
const O: ProveOptions = ProveOptions { verbose: false };

fn same(
    air: &npudr::air::Air,
    traces: Vec<p3_matrix::dense::RowMajorMatrix<npudr::field::F>>,
    cb: &[u8],
    mem: &str,
) {
    // small budgets force multi-pass quotient, grouped commit and small chunks
    unsafe { std::env::set_var("NPUDR_MEM_GB", mem) };
    let a = prover_ref::prove_bytes(air, traces.clone(), PUB, cb, &O).unwrap();
    let b = prover::prove_bytes(air, traces, PUB, cb, &O).unwrap();
    assert_eq!(a.len(), b.len());
    assert!(a == b, "proofs differ");
    npudr::verifier::verify(air, PUB, cb, &b).unwrap();
}

#[test]
fn lowmem_equals_reference() {
    for mem in ["10", "0.0005", "0.00002"] {
        let air = toy::multi_air();
        let (tr, last) = toy::fib_trace(9, 1, 1);
        let cb = toy::fib_claim(1, 1, last);
        same(
            &air,
            vec![tr, toy::cube_trace(3, 6), toy::cube_trace(1, 1)],
            &cb,
            mem,
        );
        let bus = toy::bus_air();
        let xs: Vec<u32> = (0..256u32).map(|i| (i * 7) % 64).collect();
        same(&bus, toy::bus_traces(6, 8, &xs), &[], mem);
        let (tr, last) = toy::fib_trace(13, 1, 1);
        let cb = toy::fib_claim(1, 1, last);
        same(&toy::fib_air(), vec![tr], &cb, mem);
    }
}
