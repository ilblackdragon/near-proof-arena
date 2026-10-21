use openvm_recursion_circuit::nv::circuit::NvCircuit;
use openvm_stark_backend::{
    CertSet, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
    interaction::LogUpSecurityParameters,
};

/// Same real-settings tail as the G2 gate, with the production 2^30 interaction budget.
/// No environment variable may silently reduce the security target.
pub fn params(final_layer: bool, cert_file: &str, exclusions: &str) -> SystemParams {
    shaped_params(
        final_layer,
        18,
        4096,
        NvCircuit::new(4, 18, 1).layout().degree().max(6),
        cert_file,
        exclusions,
    )
}

pub fn shaped_params(
    final_layer: bool,
    n_stack: usize,
    w_stack: usize,
    degree: usize,
    cert_file: &str,
    exclusions: &str,
) -> SystemParams {
    assert!(
        n_stack <= 18,
        "chunk shape exceeds the supported BabyBear extended domain"
    );
    let parse = |s: &str| -> Option<(u64, u64, u64)> {
        let a: Vec<_> = s.trim().split(',').collect();
        if a.len() != 4 || a[3] != "1" {
            return None;
        }
        Some((a[0].parse().ok()?, a[1].parse().ok()?, a[2].parse().ok()?))
    };
    let certs: serde_json::Value =
        serde_json::from_slice(&std::fs::read(cert_file).unwrap()).unwrap();
    let mut certs: CertSet = certs
        .as_object()
        .unwrap()
        .keys()
        .filter_map(|k| parse(k))
        .collect();
    for l in std::fs::read_to_string(exclusions).unwrap().lines() {
        if let Some(c) = parse(l) {
            certs.remove(&c);
        }
    }
    assert!(!certs.is_empty(), "no kernel-backed certificates");
    let (l_skip, log_blowup, k) = (2, 7, 4);
    let levers = WhirLevers {
        k_first: if final_layer { 1 } else { 2 },
        multiproof: true,
        keep_domain: true,
        gruen_gkr: true,
        gkr_derive_claims: true,
        next_mask: true,
        gruen_zerocheck: true,
        wide_query_pow: true,
        tight_heights: true,
        whir_y: true,
    };
    let whir = WhirConfig::new_full(
        log_blowup,
        l_skip + n_stack,
        WhirParams {
            k,
            log_final_poly_len: if final_layer { 7 } else { 6 },
            query_phase_pow_bits: 32,
            folding_pow_bits: 0,
            mu_pow_bits: 0,
            proximity: WhirProximityStrategy::ListDecoding { m: 64 },
        },
        268,
        levers,
        15,
    )
    .with_first_order(
        log_blowup,
        l_skip + n_stack,
        268,
        50,
        64,
        Some(&certs),
        if final_layer { 1 } else { 2 },
    );
    SystemParams {
        l_skip,
        n_stack,
        w_stack,
        log_blowup,
        whir,
        logup: LogUpSecurityParameters {
            max_interaction_count: 1 << 30,
            log_max_message_length: 7,
            pow_bits: 0,
        },
        max_constraint_degree: degree,
    }
}
