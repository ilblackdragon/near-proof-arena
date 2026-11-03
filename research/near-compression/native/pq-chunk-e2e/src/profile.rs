use openvm_recursion_circuit::nv::circuit::NvCircuit;
use openvm_stark_backend::{
    CertSet, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
    interaction::LogUpSecurityParameters,
};

/// Recursion-layer geometry. `NEARPROOF_CHAIN_GEOM=ns19lb6` raises the stacked ceiling of every
/// recursion layer (L1.. and FINAL) from 2^20 to 2^21 at rate 1/64 (l_skip + n_stack + log_blowup
/// stays 27, the field's two-adicity), the escape measured for depth-2 aggregation
/// (`docs/logs/pq-agg-depth2-legal-2026-10-24.md`). Chunks with receipts need it: their L1 SHA AIR
/// is 2^21 rows. Default: the delivered `ns18/lb7` geometry. The base layer is never affected.
pub fn chain_geom() -> (usize, usize) {
    match std::env::var("NEARPROOF_CHAIN_GEOM").as_deref() {
        Ok("ns19lb6") => (19, 6),
        Ok("ns18lb7") | Err(_) => (18, 7),
        Ok(other) => panic!("unknown NEARPROOF_CHAIN_GEOM {other}"),
    }
}

/// Same real-settings tail as the G2 gate, with the production 2^30 interaction budget.
/// No environment variable may silently reduce the security target.
pub fn params(final_layer: bool, cert_file: &str, exclusions: &str) -> SystemParams {
    let (n_stack, log_blowup) = chain_geom();
    shaped_params_geom(
        final_layer,
        n_stack,
        log_blowup,
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
    shaped_params_geom(final_layer, n_stack, 7, w_stack, degree, cert_file, exclusions)
}

fn shaped_params_geom(
    final_layer: bool,
    n_stack: usize,
    log_blowup: usize,
    w_stack: usize,
    degree: usize,
    cert_file: &str,
    exclusions: &str,
) -> SystemParams {
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
    let (l_skip, k) = (2, 4);
    assert!(l_skip + n_stack + log_blowup <= 27, "beyond the BabyBear two-adic domain");
    // Keep four WHIR rounds when the stacked height grows by one bit (ns19): one more bit folded
    // into the final polynomial.
    let extra = (l_skip + n_stack).saturating_sub(20);
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
            log_final_poly_len: if final_layer { 7 } else { 6 } + extra,
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
