//! near-arena-oracle-v3-d0a: domain-D0a variant of the judge-owned oracle for `near/pv86/chunk-validation/v0`
//! (spec/near-chunk-validation-v0.md, spec/claim-v3.md).
//!
//! The reference judge is nearcore's own stateless validator
//! (`pre_validate_chunk_state_witness` + `validate_chunk_state_witness`, the
//! witness path of `ChunkValidationActor`). Witnesses are the real
//! `ChunkStateWitness` values that chunk producers emit in a multi-shard
//! nearcore `TestEnv` (real NightshadeRuntime, epoch manager, block/chunk
//! production), serialized with nearcore borsh.
//!
//! Commands:
//!   gen    --seed S --out DIR [--chains K] [--blocks N] [--ood-cap C] [--mutate-every M]
//!          Generate cases: DIR/d0/* (honest, in D0), DIR/ood/* (honest, out of D0,
//!          capped per violation family), DIR/mutants/* (derived from D0 cases),
//!          each with claim.bin, witness.bin, meta.json; DIR/summary.json.
//!          Arena (judge) mode, used by runners/worker `NearV3Oracle` and the
//!          spec/workloads/near-chunk-validation-d0 generator specs:
//!            --fixtures-layout     DIR/cases/<n>/{request,witness,expected_claim}.bin
//!                                  (expected_rel_d0 = true; request = claim) and
//!                                  DIR/rejections/<n>/{request,witness}.bin (false)
//!            --class any|quiet|transfers|missing   honest positives of that class only
//!            --d0-target N         stop after N honest positives
//!            --rejection-target R  stop after R rejections (with --d0-target: both)
//!            --per-chain-cap K     at most K honest positives per chain
//!            --no-positives        rejections only
//!            --accepted-mutants    also write nearcore-accepted D0 mutants as positives
//!            --rotate              chain k uses parameter set (k + seed) mod 12
//!                                  (shards 4/5/6 x RS seats 8/100/16/3) instead of k
//!            --p-missing P         per-client probability of skipping a chunk (default 0.12)
//!   vectors --out DIR [--seed S]
//!          Leaf-primitive vectors from nearcore code (src/vectors.rs).
//!   params --out FILE
//!          Runtime-config description for runtime_config_digest_v3.

// Domain D0a (spec/near-chunk-validation-v0a.md): RelD0a = RelD0 ∧ A1 ∧ A2 ∧ Canon0f.
// Shared, unmodified, with the D0 oracle (oracle/v3/src, pinned by the live D0 challenges):
#[path = "../../v3/src/claim.rs"]
mod claim;
#[path = "../../v3/src/d0.rs"]
mod d0;
#[path = "../../v3/src/enc.rs"]
mod enc;
#[path = "../../v3/src/judge.rs"]
mod judge;
#[path = "../../v3/src/mutate.rs"]
mod mutate;
#[path = "../../v3/src/vectors.rs"]
mod vectors;
// D0a (this crate): chain generation copied from ../v3/src/chaingen.rs with the D0a
// classification, the A1 chain and the A2 mutant; amendment classifier; A2 mutant.
mod a2mut;
mod chaingen;
mod d0a;

use serde_json::json;
use std::path::PathBuf;

const NEARCORE_COMMIT: &str = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993";

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

fn chain_params(seed: u64, i: usize, blocks: u64, p_missing: f64) -> chaingen::ChainParams {
    let seats = [8u64, 100, 16, 3][i % 4];
    chaingen::ChainParams {
        seed: seed.wrapping_mul(1_000_003).wrapping_add(i as u64),
        n_shards: [4usize, 5, 6][i % 3],
        seats,
        // chain 8 (A1): genesis gas limit 1500 Tgas > 10^15 -- every chunk out of D0a (c.gas_limit)
        gas_limit_tgas: if i == 8 { 1500 } else if i % 4 == 3 { 10 } else { 1000 },
        epoch_length: 30,
        blocks,
        p_missing,
        p_tx_shard: 0.35,
        p_burst: 0.08,
        p_fail: 0.02,
        p_implicit: 0.01,
        p_two: 0.02,
        long_skip: if i % 8 == 5 { Some((40, 40, 0)) } else { None },
    }
}

fn cmd_gen(args: &[String]) -> i32 {
    let seed: u64 = arg(args, "--seed").and_then(|s| s.parse().ok()).unwrap_or(1);
    let out = PathBuf::from(arg(args, "--out").expect("--out"));
    let chains: usize = arg(args, "--chains").and_then(|s| s.parse().ok()).unwrap_or(6);
    let blocks: u64 = arg(args, "--blocks").and_then(|s| s.parse().ok()).unwrap_or(100);
    let ood_cap: usize = arg(args, "--ood-cap").and_then(|s| s.parse().ok()).unwrap_or(20);
    let mutate_every: usize = arg(args, "--mutate-every").and_then(|s| s.parse().ok()).unwrap_or(6);
    let flag = |n: &str| args.iter().any(|a| a == n);
    let num = |n: &str| -> usize {
        match arg(args, n) {
            None => 0,
            Some(v) => v.parse().unwrap_or_else(|_| panic!("{n}: not a number: {v}")),
        }
    };
    let class = match arg(args, "--class") {
        None => chaingen::CaseClass::Any,
        Some(c) => chaingen::CaseClass::parse(&c).unwrap_or_else(|| panic!("--class: unknown class {c}")),
    };
    let p_missing: f64 = arg(args, "--p-missing").map(|s| s.parse().expect("--p-missing")).unwrap_or(0.12);
    let opts = chaingen::GenOpts {
        ood_cap,
        mutate_every,
        fixtures_layout: flag("--fixtures-layout"),
        class,
        no_positives: flag("--no-positives"),
        accepted_mutants: flag("--accepted-mutants"),
        positive_target: num("--d0-target"),
        rejection_target: num("--rejection-target"),
        per_chain_cap: num("--per-chain-cap"),
    };
    let rotate = flag("--rotate");
    std::fs::create_dir_all(&out).unwrap();
    let mut stats = chaingen::Stats {
        honest: 0,
        honest_ok: 0,
        d0: 0,
        ood_written: 0,
        mutants: 0,
        by_violation: Default::default(),
        positives: 0,
        rejections: 0,
    };
    let mut params = Vec::new();
    for i in 0..chains {
        if opts.done(&stats) {
            break;
        }
        let k = if rotate { (i as u64 + seed % 12) as usize } else { i };
        let mut p = chain_params(seed, k, blocks, p_missing);
        // the chain seed stays tied to the chain's position in this run
        p.seed = seed.wrapping_mul(1_000_003).wrapping_add(i as u64);
        eprintln!("chain {i}: {p:?}");
        params.push(format!("{p:?}"));
        chaingen::run_chain(i, &p, &out, &opts, &mut stats);
        eprintln!(
            "  honest={} ok={} d0={} ood_written={} mutants={}",
            stats.honest, stats.honest_ok, stats.d0, stats.ood_written, stats.mutants
        );
    }
    let mut summary = json!({
        "nearcore_commit": NEARCORE_COMMIT, "protocol_version": 86, "seed": seed,
        "chains": params, "honest_witnesses": stats.honest, "honest_accepted_by_nearcore": stats.honest_ok,
        "d0_cases": stats.d0, "ood_cases_written": stats.ood_written, "mutants": stats.mutants,
        "d0_violation_counts": stats.by_violation,
    });
    if opts.fixtures_layout {
        summary["arena_layout"] = json!({
            "class": format!("{:?}", opts.class), "positives": stats.positives, "rejections": stats.rejections,
            "d0_target": opts.positive_target, "rejection_target": opts.rejection_target,
            "accepted_mutants": opts.accepted_mutants, "rotate": rotate, "p_missing": p_missing,
            "per_chain_cap": opts.per_chain_cap,
        });
    }
    std::fs::write(out.join("summary.json"), serde_json::to_string_pretty(&summary).unwrap()).unwrap();
    if stats.honest_ok != stats.honest {
        eprintln!("WARNING: some honest witnesses were rejected by nearcore");
        return 1;
    }
    if opts.fixtures_layout
        && (stats.positives < opts.positive_target || stats.rejections < opts.rejection_target)
    {
        eprintln!(
            "targets not reached: {} of {} positives, {} of {} rejections (raise --chains)",
            stats.positives, opts.positive_target, stats.rejections, opts.rejection_target
        );
        return 3;
    }
    0
}

fn cmd_params(args: &[String]) -> i32 {
    let out = PathBuf::from(arg(args, "--out").expect("--out"));
    let store = near_parameters::RuntimeConfigStore::new(None);
    let cfg = store.get_config(86);
    let cc = &cfg.congestion_control_config;
    let bw = &cfg.bandwidth_scheduler_config;
    let view = near_parameters::view::RuntimeConfigView::from(cfg.as_ref().clone());
    let view_json = serde_json::to_vec(&view).unwrap();
    let d = json!({
        "schema": "near-arena-runtime-config-v3",
        "nearcore_commit": NEARCORE_COMMIT,
        "protocol_version": 86,
        "runtime_config_view_sha256": hex::encode(enc::sha256(&view_json)),
        "congestion_control": {
            "max_congestion_incoming_gas": cc.max_congestion_incoming_gas.as_gas(),
            "max_congestion_outgoing_gas": cc.max_congestion_outgoing_gas.as_gas(),
            "max_congestion_memory_consumption": cc.max_congestion_memory_consumption,
            "max_congestion_missed_chunks": cc.max_congestion_missed_chunks,
            "max_outgoing_gas": cc.max_outgoing_gas.as_gas(),
            "min_outgoing_gas": cc.min_outgoing_gas.as_gas(),
            "allowed_shard_outgoing_gas": cc.allowed_shard_outgoing_gas.as_gas(),
        },
        "bandwidth_scheduler": {
            "max_shard_bandwidth": bw.max_shard_bandwidth,
            "max_single_grant": bw.max_single_grant,
            "max_allowance": bw.max_allowance,
            "max_base_bandwidth": bw.max_base_bandwidth,
        },
        "max_receipt_size": cfg.wasm_config.limit_config.max_receipt_size,
        "main_storage_proof_size_soft_limit": cfg.witness_config.main_storage_proof_size_soft_limit,
    });
    std::fs::write(&out, serde_json::to_string_pretty(&d).unwrap()).unwrap();
    0
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = match args.get(1).map(String::as_str) {
        Some("gen") => cmd_gen(&args),
        Some("params") => cmd_params(&args),
        Some("vectors") => vectors::cmd_vectors(
            &PathBuf::from(arg(&args, "--out").expect("--out")),
            arg(&args, "--seed").and_then(|s| s.parse().ok()).unwrap_or(1),
        ),
        _ => {
            eprintln!("usage: near-arena-oracle-v3 gen|params ... (see src/main.rs)");
            2
        }
    };
    std::process::exit(code);
}
