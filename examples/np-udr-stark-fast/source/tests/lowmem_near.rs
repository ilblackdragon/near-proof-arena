//! On NEAR workloads (public fixtures and a generated case with large
//! tables), the low-memory prover's proofs equal the reference prover's,
//! at the default budget and at a tiny one (multi-pass quotient).
use npudr::near::{self, genmax};
use npudr::prover::{self, ProveOptions};
use npudr::prover_ref;

const PUB: &[u8] = b"public tape";
const O: ProveOptions = ProveOptions { verbose: false };

fn fixture(name: &str) -> (Vec<u8>, Vec<u8>) {
    let d = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../oracle/fixtures/public/cases").join(name);
    (std::fs::read(d.join("request.bin")).unwrap(), std::fs::read(d.join("witness.bin")).unwrap())
}

fn same(name: &str, req: &[u8], wit: &[u8]) {
    let (cb, air, rows) = near::prepare(req, wit).unwrap_or_else(|e| panic!("{name}: {e}"));
    let a = prover_ref::prove_bytes(&air, rows, PUB, &cb, &O).unwrap();
    npudr::verifier::verify(&air, PUB, &cb, &a).unwrap();
    for mem in ["11", "0.0005"] {
        unsafe { std::env::set_var("NPUDR_MEM_GB", mem) };
        let (cb2, air2, cols) = near::prepare_cols(req, wit).unwrap();
        assert_eq!(cb, cb2);
        let b = prover::prove_cols_bytes(&air2, cols, PUB, &cb2, &O).unwrap();
        assert!(a == b, "{name} (budget {mem} GB): proofs differ");
    }
}

#[test]
fn lowmem_equals_reference_near() {
    for name in ["s20261003-v4", "s20261003-v5", "s20261003-v17"] {
        let (r, w) = fixture(name);
        same(name, &r, &w);
    }
    let g = genmax::gen_max(&genmax::Opts { target_bytes: 60_000, n: Some(5), ..Default::default() }).unwrap();
    same("gen-max 60k", &g.request, &g.witness);
}
