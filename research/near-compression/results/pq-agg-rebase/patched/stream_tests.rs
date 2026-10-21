//! [stream research] SHA-384 / Ext12 configs: streamed commitments (codeword never materialised)
//! give byte-identical proofs to the in-memory prover. Process SHA levers (42-B digests, coset
//! leaves, T*) come from the env, as for the other NV tests.
use openvm_stark_backend::{
    codec::Encode,
    prover::stream_pcs::set_stream_override,
    test_utils::{FibFixture, InteractionsFixture11, TestFixture},
    StarkEngine, WhirLevers,
};

use crate::sha384::{config::*, e2e_tests::with_levers};

/// b = 2 (rate 1/4), small trace, every WHIR lever with the x15 domain and a wide query PoW;
/// the final-layer engine too. Streamed (drop 0 / 3 / 4 levels) == in-memory, byte for byte.
#[test]
fn stream_commit_matches_in_memory_b2() {
    let lv = WhirLevers {
        k_first: 1,
        keep_domain: true,
        multiproof: true,
        gruen_gkr: true,
        gkr_derive_claims: true,
        gruen_zerocheck: true,
        next_mask: true,
        wide_query_pow: true,
        tight_heights: true,
        whir_y: true,
    };
    for (name, lv, x15, k) in [("default", WhirLevers::default(), 1, 3), ("all+x15", lv, 15, 3), ("all+x15 k4", lv, 15, 4)] {
        let mut p = openvm_stark_backend::test_utils::test_system_params_small(2, 10, k);
        p.max_constraint_degree = 4;
        p.log_blowup = 2;
        let mut p = with_levers(p, lv, x15, 40);
        if lv.wide_query_pow {
            p.whir.query_phase_pow_bits = 8;
        }
        for fin in [false, true] {
            for fx in 0..2 {
                let prove = |stream: bool| -> Vec<u8> {
                    set_stream_override(Some(stream));
                    let e = if fin { Sha384CpuEngine::new_final(p.clone()) } else { Sha384CpuEngine::new(p.clone()) };
                    let (vk, pr) = if fx == 0 {
                        FibFixture::new(0, 1, 1 << 9).keygen_and_prove(&e)
                    } else {
                        InteractionsFixture11.keygen_and_prove(&e)
                    };
                    e.verify(&vk, &pr).expect("proof verifies");
                    set_stream_override(None);
                    let mut b = vec![];
                    pr.encode(&mut b).unwrap();
                    b
                };
                let mem = prove(false);
                for drop in ["0", "3", "4"] {
                    std::env::set_var("NEARPROOF_STREAM_DROP", drop);
                    let st = prove(true);
                    println!("STREAM_IDENTITY case={name} final={fin} fixture={fx} drop={drop} bytes={} identical={}", mem.len(), mem == st);
                    assert_eq!(mem, st, "streamed proof differs: {name} final={fin} fixture {fx} drop {drop}");
                }
                std::env::remove_var("NEARPROOF_STREAM_DROP");
            }
        }
    }
}

/// Prints the committed (tight) heights and component sizes of a saved proof (env PROOF=path).
#[test]
#[ignore]
fn stream_proof_info() {
    use openvm_stark_backend::{codec::Decode, proof::Proof};
    let path = std::env::var("PROOF").expect("PROOF=<path>");
    let bytes = std::fs::read(&path).unwrap();
    let p = Proof::<Sha384Config>::decode(&mut std::io::Cursor::new(&bytes)).unwrap();
    for (i, t) in p.trace_vdata.iter().enumerate() {
        if let Some(t) = t {
            println!("PROOF_INFO air={i} log_height={} committed_rows={:?}", t.log_height, t.tight_height);
        }
    }
    println!("PROOF_INFO bytes={} {}", bytes.len(), crate::sha384::e2e_tests::proof_sizes(&p));
}
