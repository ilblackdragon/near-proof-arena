//! Independent in-memory/streamed proof parity for the allocation experiment.
use openvm_recursion_circuit::sha384::config::Sha384CpuEngine;
use openvm_stark_backend::{
    StarkEngine, WhirLevers,
    codec::Encode,
    prover::stream_pcs::set_stream_override,
    test_utils::{FibFixture, InteractionsFixture11, TestFixture, test_system_params_small},
};

pub fn run() {
    for odd in [1, 15] {
        for final_layer in [false, true] {
            for fixture in [0, 1] {
                let mut params = test_system_params_small(2, 10, 3);
                params.max_constraint_degree = 4;
                params.log_blowup = 2;
                let levers = WhirLevers {
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
                let w = &params.whir;
                let h = params.l_skip + params.n_stack;
                let lf = params.log_final_poly_len();
                let wp = openvm_stark_backend::WhirParams {
                    k: w.k,
                    log_final_poly_len: lf + (h - levers.k_first - lf) % w.k,
                    proximity: w.proximity,
                    query_phase_pow_bits: 8,
                    folding_pow_bits: w.folding_pow_bits,
                    mu_pow_bits: w.mu_pow_bits,
                };
                // Small differential-test parameters only; production profile is untouched.
                params.whir = openvm_stark_backend::WhirConfig::new_full(
                    params.log_blowup,
                    h,
                    wp,
                    40,
                    levers,
                    odd,
                );
                let prove = |stream| {
                    set_stream_override(Some(stream));
                    let engine = if final_layer {
                        Sha384CpuEngine::new_final(params.clone())
                    } else {
                        Sha384CpuEngine::new(params.clone())
                    };
                    let (vk, proof) = if fixture == 0 {
                        FibFixture::new(0, 1, 1 << 9).keygen_and_prove(&engine)
                    } else {
                        InteractionsFixture11.keygen_and_prove(&engine)
                    };
                    engine
                        .verify(&vk, &proof)
                        .expect("independent verification");
                    let mut bytes = vec![];
                    proof.encode(&mut bytes).unwrap();
                    bytes
                };
                let reference = prove(false);
                assert_eq!(reference, prove(true), "streamed commitment parity");
                println!("STREAM_PARITY_OK odd={odd} final={final_layer} fixture={fixture}");
            }
        }
    }
    set_stream_override(None);
}
