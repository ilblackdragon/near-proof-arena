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
/// [E2E-D] `NEARPROOF_ZK=1` (the driver's default): PCS-level hiding where it is needed for a
/// published packet. The base commits with `zk = 1` (random reserved rows: its root, hence the
/// published stacking point u, is a random-oracle output on an unpredictable input); the FINAL
/// layer with `zk = 2` (reserved rows + 12 uniform mask columns). Inner NV levels are never
/// published and stay `zk = 0`. `NEARPROOF_ZK=0` reproduces the 2026-10-31 parameters exactly.
pub fn zk_lever() -> bool {
    std::env::var("NEARPROOF_ZK").map(|v| v == "1").unwrap_or(false)
}

pub fn params(final_layer: bool, cert_file: &str, exclusions: &str) -> SystemParams {
    params_geom(final_layer, cert_file, exclusions, chain_geom())
}

/// [E2E-D D-5] The tree layer's geometry (`NEARPROOF_TREE_GEOM`, default `ns20lb5`): an arity-2
/// node verifies two children whose SHA work alone is about 2 x 1.06M rows, just above the
/// 2^21-row stacked ceiling of `ns19lb6`, so the tree proofs stack at 2^22 at rate 1/32
/// (`l_skip + n_stack + log_blowup` stays 27). Query counts and every per-round bound come from
/// the same calibration (`WhirConfig::new_full` + first-order certificates) at the 268-bit target.
/// [E2E-D D-8] `nsXXlbY` -> `(XX, Y)` (any geometry; `shaped_params_geom` checks the two-adic bound).
pub fn parse_geom(s: &str) -> (usize, usize) {
    let r = s.strip_prefix("ns").and_then(|x| x.split_once("lb")).and_then(|(a, b)| Some((a.parse().ok()?, b.parse().ok()?)));
    r.unwrap_or_else(|| panic!("geometry {s}: expected nsXXlbY"))
}

pub fn tree_geom() -> (usize, usize) {
    match std::env::var("NEARPROOF_TREE_GEOM").as_deref() {
        Ok("ns20lb5") | Err(_) => (20, 5),
        Ok("ns19lb6") => (19, 6),
        Ok(other) => panic!("unknown NEARPROOF_TREE_GEOM {other}"),
    }
}

/// [`params`] at an explicit `(n_stack, log_blowup)`.
pub fn params_geom(final_layer: bool, cert_file: &str, exclusions: &str, geom: (usize, usize)) -> SystemParams {
    let (n_stack, log_blowup) = geom;
    // NEARPROOF_ZK_FINAL overrides the FINAL mode (3 = 2 + slice splitting in the packing)
    let zk_final = std::env::var("NEARPROOF_ZK_FINAL").ok().and_then(|v| v.parse().ok()).unwrap_or(2u8);
    let zk = if final_layer && zk_lever() { zk_final } else { 0 };
    shaped_params_geom(
        zk,
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
    // [E2E-D D-8] the base geometry bound is the two-adic one, 2 + n_stack + log_blowup <= 27 (at the
    // pinned lb 7: n_stack <= 18; a large-class base at n_stack 22 runs at lb <= 3)
    assert!(
        2 + n_stack + base_log_blowup() <= 27,
        "chunk shape exceeds the supported BabyBear extended domain (n_stack {n_stack}, lb {})",
        base_log_blowup()
    );
    // only the base calls this (`chunk_bridge::prove_base`)
    // [E2E-D D-5] NEARPROOF_ZK_BASE=2: the QROM option "base zk = 2" (ZK-ARGUMENT 6.5.6), off by
    // default; measured only, not adopted (owner decision)
    let zk_base = std::env::var("NEARPROOF_ZK_BASE").ok().and_then(|v| v.parse().ok()).unwrap_or(1u8);
    let zk = if !final_layer && zk_lever() { zk_base } else { 0 };
    shaped_params_geom(zk, final_layer, n_stack, base_log_blowup(), w_stack, degree, cert_file, exclusions)
}

/// [E2E-D D-8] The base layer's log blowup: the pinned 7, or `NEARPROOF_BASE_LB` (a measurement
/// lever for the leaf-cost law, off by default; the 268-bit per-round target, the proximity
/// strategy and the grinding are unchanged, so the query counts follow from the rate).
pub fn base_log_blowup() -> usize {
    // a class may pin its base rate (`"log_blowup"` in the class file, for a class whose stacked
    // height needs n_stack 22)
    if let Some(lb) = std::env::var("NEARPROOF_BASE_CLASS")
        .ok()
        .and_then(|p| std::fs::read(p).ok())
        .and_then(|b| serde_json::from_slice::<serde_json::Value>(&b).ok())
        .and_then(|v| v.get("log_blowup").and_then(|x| x.as_u64()))
    {
        assert!(std::env::var("NEARPROOF_BASE_LB").is_err(), "NEARPROOF_BASE_LB and a class log_blowup");
        return lb as usize;
    }
    match std::env::var("NEARPROOF_BASE_LB") {
        Ok(v) => {
            let lb: usize = v.parse().expect("NEARPROOF_BASE_LB");
            assert!((1..=7).contains(&lb), "NEARPROOF_BASE_LB in 1..=7");
            lb
        }
        Err(_) => 7,
    }
}

/// [E2E-D D-8] `base-whir` only: the query-phase grinding bits of the parameter table
/// (`NEARPROOF_BASE_WHIR_POW`, read only while `base_params_at` builds a table row; never set
/// when proving: the pinned 32 bits apply).
fn table_pow_bits() -> Option<usize> {
    if !TABLE_MODE.load(std::sync::atomic::Ordering::Relaxed) {
        return None;
    }
    std::env::var("NEARPROOF_BASE_WHIR_POW").ok().map(|v| v.parse().expect("NEARPROOF_BASE_WHIR_POW"))
}

static TABLE_MODE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// [E2E-D D-8] The base parameters at an explicit `(n_stack, log_blowup)` (any geometry within the
/// two-adic domain; for the `base-whir` table, never used to prove).
pub fn base_params_at(n_stack: usize, log_blowup: usize, w_stack: usize, degree: usize, cert_file: &str, exclusions: &str) -> SystemParams {
    let zk = if zk_lever() { 1 } else { 0 };
    TABLE_MODE.store(true, std::sync::atomic::Ordering::Relaxed);
    let p = shaped_params_geom(zk, false, n_stack, log_blowup, w_stack, degree, cert_file, exclusions);
    TABLE_MODE.store(false, std::sync::atomic::Ordering::Relaxed);
    p
}

#[allow(clippy::too_many_arguments)]
fn shaped_params_geom(
    zk: u8,
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
    // [E2E-D] per-round soundness target of the FINAL layer (bits); NEARPROOF_FINAL_RBR overrides
    // the pinned 268 to measure the size at a higher target (e.g. 274, E2E-SOUNDNESS-BUDGET.md)
    let rbr_target: usize = if final_layer {
        std::env::var("NEARPROOF_FINAL_RBR").ok().and_then(|v| v.parse().ok()).unwrap_or(268)
    } else {
        268
    };
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
        zk,
    };
    let whir = WhirConfig::new_full(
        log_blowup,
        l_skip + n_stack,
        WhirParams {
            k,
            log_final_poly_len: if final_layer { 7 } else { 6 } + extra,
            query_phase_pow_bits: table_pow_bits().unwrap_or(32),
            folding_pow_bits: 0,
            mu_pow_bits: 0,
            proximity: WhirProximityStrategy::ListDecoding { m: 64 },
        },
        rbr_target,
        levers,
        15,
    )
    .with_first_order(
        log_blowup,
        l_skip + n_stack,
        rbr_target,
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
