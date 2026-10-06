//! near-arena-oracle-v3: judge-owned oracle for `near/pv86/chunk-validation/v0`
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
//!          Domain D1 (spec/near-chunk-validation-d1.md): --domain d1 writes DIR/d1/*,
//!          DIR/ood/*, DIR/mutants/* with Transfer transactions of every validity class
//!          (src/d1gen.rs, src/d1.rs); without it the D0 output is unchanged.
//!   ed25519-judge --in IN.jsonl --out OUT.jsonl / ed25519-sign --seed S --n N --out F
//!          nearcore's Ed25519 verdicts / signatures (src/ed25519v.rs).
//!   vectors --out DIR [--seed S]
//!          Leaf-primitive vectors from nearcore code (src/vectors.rs).
//!   params --out FILE [--d1]
//!          Runtime-config description for runtime_config_digest_v3.

// Shared, unmodified, with the D0 oracle (oracle/v3/src, whose tree digest the live D0
// challenge's generator specs pin): claim building, encodings, D0 classifier, judge, mutants.
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
// D1 (this crate)
mod chaind2;
mod chaingen;
mod d1;
mod d2;
mod d2gen;
mod d1gen;
mod d1judge;
mod ed25519v;

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
        gas_limit_tgas: if i % 4 == 3 { 10 } else { 1000 },
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
    // this binary generates domain D1 (`--domain d1` accepted for clarity; `--domain d0` refused)
    // or domain D2 (`--domain d2`, src/chaind2.rs; the D1 path below is untouched by it)
    if arg(args, "--domain").as_deref() == Some("d2") {
        return cmd_gen_d2(args);
    }
    if arg(args, "--domain").as_deref().is_some_and(|d| d != "d1") {
        panic!("near-arena-oracle-v3-d1 generates domain D1 only; use near-arena-oracle-v3 for D0");
    }
    let d1 = true;
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
        d1,
        p_adv: if d1 { 0.5 } else { 0.0 },
    };
    if d1 && opts.fixtures_layout {
        panic!("--domain d1 supports the difftest layout only");
    }
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
        d1: 0,
        injected: 0,
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
        let pstr = format!("{}, d1: true, p_adv: {:?} }}", format!("{p:?}").trim_end_matches(" }"), opts.p_adv);
        eprintln!("chain {i}: {pstr}");
        params.push(pstr);
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
    if d1 {
        // D1 runs: violation counts are D1's; D0 output (above) is unchanged
        summary["domain"] = json!("D1");
        summary["d1_cases"] = json!(stats.d1);
        summary["crafted_transactions"] = json!(stats.injected);
        summary["d1_violation_counts"] = summary["d0_violation_counts"].take();
        summary.as_object_mut().unwrap().remove("d0_violation_counts");
    }
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

/// Domain-D2 chain parameters of chain `i` (shards, Reed–Solomon seats, gas limits incl. low
/// ones for delayed receipts, short epochs for validator updates inside segments).
fn chain_params_d2(seed: u64, i: usize, blocks: u64, p_missing: f64) -> chaind2::D2Params {
    chaind2::D2Params {
        base: chaingen::ChainParams {
            seed: seed.wrapping_mul(1_000_003).wrapping_add(i as u64),
            n_shards: [4usize, 5, 6][i % 3],
            seats: [8u64, 100, 16, 3][i % 4],
            gas_limit_tgas: [1000u64, 1000, 1000, 10, 60][i % 5],
            epoch_length: [12u64, 30, 20][(i / 3) % 3],
            blocks,
            p_missing,
            p_tx_shard: 0.5,
            p_burst: 0.04,
            p_fail: 0.0,
            p_implicit: 0.0,
            p_two: 0.0,
            // one chain in eight: a shard's chunks missing for 40 heights (segments > 32 blocks)
            long_skip: if i % 8 == 5 { Some((60, 40, 0)) } else { None },
        },
        max_txs: 6,
        // long chains (≥ 250 blocks) call the contract more often: their early yields time out
        // 200 blocks later inside the chain
        p_contract: if blocks >= 250 { 0.10 } else { 0.04 },
        p_adv: 0.35,
    }
}

fn cmd_gen_d2(args: &[String]) -> i32 {
    let seed: u64 = arg(args, "--seed").and_then(|s| s.parse().ok()).unwrap_or(1);
    let out = PathBuf::from(arg(args, "--out").expect("--out"));
    let chains: usize = arg(args, "--chains").and_then(|s| s.parse().ok()).unwrap_or(6);
    let first: usize = arg(args, "--first-chain").and_then(|s| s.parse().ok()).unwrap_or(0);
    let blocks: u64 = arg(args, "--blocks").and_then(|s| s.parse().ok()).unwrap_or(100);
    let ood_cap: usize = arg(args, "--ood-cap").and_then(|s| s.parse().ok()).unwrap_or(20);
    let mutate_every: usize = arg(args, "--mutate-every").and_then(|s| s.parse().ok()).unwrap_or(6);
    let p_missing: f64 = arg(args, "--p-missing").map(|s| s.parse().expect("--p-missing")).unwrap_or(0.12);
    let opts = chaingen::GenOpts {
        ood_cap,
        mutate_every,
        fixtures_layout: false,
        class: chaingen::CaseClass::Any,
        no_positives: false,
        accepted_mutants: false,
        positive_target: 0,
        rejection_target: 0,
        per_chain_cap: 0,
        d1: false,
        p_adv: 0.35,
    };
    std::fs::create_dir_all(&out).unwrap();
    let mut stats = chaingen::Stats {
        honest: 0, honest_ok: 0, d0: 0, ood_written: 0, mutants: 0, by_violation: Default::default(),
        positives: 0, rejections: 0, d1: 0, injected: 0,
    };
    let mut params = Vec::new();
    for i in first..first + chains {
        let p = chain_params_d2(seed, i, blocks, p_missing);
        let pstr = format!("{p:?}");
        eprintln!("chain {i}: {pstr}");
        params.push(pstr);
        chaind2::run_chain_d2(i, &p, &out, &opts, &mut stats);
        eprintln!(
            "  honest={} ok={} d2={} d1={} d0={} ood_written={} mutants={} crafted={}",
            stats.honest, stats.honest_ok, stats.positives, stats.d1, stats.d0, stats.ood_written, stats.mutants, stats.injected
        );
    }
    let summary = json!({
        "nearcore_commit": NEARCORE_COMMIT, "protocol_version": 86, "seed": seed, "domain": "D2",
        "chains": params, "honest_witnesses": stats.honest, "honest_accepted_by_nearcore": stats.honest_ok,
        "d2_cases": stats.positives, "d1_cases_among_d2": stats.d1, "d0_cases_among_d2": stats.d0,
        "ood_cases_written": stats.ood_written, "mutants": stats.mutants,
        "crafted_transactions": stats.injected, "d2_violation_counts": stats.by_violation,
    });
    std::fs::write(out.join("summary.json"), serde_json::to_string_pretty(&summary).unwrap()).unwrap();
    if stats.honest_ok != stats.honest {
        eprintln!("WARNING: some honest witnesses were rejected by nearcore");
        return 1;
    }
    0
}

/// Fee parameters read by Transfer-transaction conversion (domain D1): `tx_cost`
/// (runtime/runtime/src/config.rs:400-479) and the limits checked on transactions.
fn d1_fees(cfg: &near_parameters::RuntimeConfig) -> serde_json::Value {
    use near_parameters::{ActionCosts, SignatureKind};
    let f = |c: ActionCosts| {
        let fee = cfg.fees.fee(c);
        let pc = |p: near_parameters::ParameterCost| json!([p.gas.as_gas(), p.compute]);
        json!({"send_sir": pc(fee.send_fee(true)), "send_not_sir": pc(fee.send_fee(false)), "exec": pc(fee.exec_fee())})
    };
    let sv = |k: SignatureKind| {
        let p = cfg.fees.signature_verification_costs[k];
        json!([p.gas.as_gas(), p.compute])
    };
    json!({
        "new_action_receipt": f(ActionCosts::new_action_receipt),
        "transfer": f(ActionCosts::transfer),
        "create_account": f(ActionCosts::create_account),
        "add_full_access_key": f(ActionCosts::add_full_access_key),
        "signature_verification": {"ed25519": sv(SignatureKind::Ed25519), "secp256k1": sv(SignatureKind::Secp256k1), "mldsa65": sv(SignatureKind::MlDsa65)},
        "min_gas_purchase_price": cfg.min_gas_purchase_price.as_yoctonear().to_string(),
        "storage_amount_per_byte": cfg.storage_amount_per_byte().as_yoctonear().to_string(),
        "eth_implicit_accounts": cfg.wasm_config.eth_implicit_accounts,
        "max_transaction_size": cfg.wasm_config.limit_config.max_transaction_size,
        "max_actions_per_receipt": cfg.wasm_config.limit_config.max_actions_per_receipt,
        "access_key_nonce_range_multiplier": near_primitives::account::AccessKey::ACCESS_KEY_NONCE_RANGE_MULTIPLIER,
    })
}

/// Every runtime parameter the D2 relation reads (fees with gas and compute, storage, limits,
/// refunds, account creation, gas keys, wallet contract hashes), from nearcore's own config.
fn d2_params(cfg: &near_parameters::RuntimeConfig) -> serde_json::Value {
    use near_parameters::{ActionCosts, ExtCosts, SignatureKind};
    use strum::IntoEnumIterator;
    let mut fees = serde_json::Map::new();
    for c in ActionCosts::iter() {
        let fee = cfg.fees.fee(c);
        let pc = |p: near_parameters::ParameterCost| json!([p.gas.as_gas(), p.compute]);
        fees.insert(format!("{c:?}"), json!({"send_sir": pc(fee.send_fee(true)), "send_not_sir": pc(fee.send_fee(false)), "exec": pc(fee.exec_fee())}));
    }
    let sv = |k: SignatureKind| {
        let p = cfg.fees.signature_verification_costs[k];
        json!([p.gas.as_gas(), p.compute])
    };
    let ext = |e: ExtCosts| json!([cfg.wasm_config.ext_costs.gas_cost(e).as_gas(), cfg.wasm_config.ext_costs.compute_cost(e)]);
    let su = &cfg.fees.storage_usage_config;
    let lc = &cfg.wasm_config.limit_config;
    let acc = &cfg.account_creation_config;
    json!({
        "action_fees": fees,
        "signature_verification": {"ed25519": sv(SignatureKind::Ed25519), "secp256k1": sv(SignatureKind::Secp256k1), "mldsa65": sv(SignatureKind::MlDsa65)},
        "ext_storage_remove": {"base": ext(ExtCosts::storage_remove_base), "key_byte": ext(ExtCosts::storage_remove_key_byte), "ret_value_byte": ext(ExtCosts::storage_remove_ret_value_byte)},
        "storage_usage": {"num_bytes_account": su.num_bytes_account, "num_extra_bytes_record": su.num_extra_bytes_record,
            "storage_amount_per_byte": su.storage_amount_per_byte.as_yoctonear().to_string(),
            "global_contract_storage_amount_per_byte": su.global_contract_storage_amount_per_byte.as_yoctonear().to_string()},
        "burnt_gas_reward": [*cfg.fees.burnt_gas_reward.numer(), *cfg.fees.burnt_gas_reward.denom()],
        "gas_refund_penalty": [*cfg.fees.gas_refund_penalty.numer(), *cfg.fees.gas_refund_penalty.denom()],
        "min_gas_refund_penalty": cfg.fees.min_gas_refund_penalty.as_gas(),
        "min_gas_purchase_price": cfg.min_gas_purchase_price.as_yoctonear().to_string(),
        "account_creation_charge": cfg.account_creation_charge.as_yoctonear().to_string(),
        "use_state_stored_receipt": cfg.use_state_stored_receipt,
        "account_creation": {"min_allowed_top_level_account_length": acc.min_allowed_top_level_account_length, "registrar_account_id": acc.registrar_account_id.to_string()},
        "limits": {"max_actions_per_receipt": lc.max_actions_per_receipt, "max_total_prepaid_gas": lc.max_total_prepaid_gas.as_gas(),
            "max_number_bytes_method_names": lc.max_number_bytes_method_names, "max_length_method_name": lc.max_length_method_name,
            "max_arguments_length": lc.max_arguments_length, "max_length_returned_data": lc.max_length_returned_data,
            "max_contract_size": lc.max_contract_size, "max_transaction_size": lc.max_transaction_size,
            "max_receipt_size": lc.max_receipt_size, "max_number_input_data_dependencies": lc.max_number_input_data_dependencies,
            "max_deploy_actions_per_receipt": lc.max_deploy_actions_per_receipt, "yield_timeout_length_in_blocks": lc.yield_timeout_length_in_blocks,
            "account_id_validity_rules_version": format!("{:?}", lc.account_id_validity_rules_version)},
        "eth_implicit_accounts": cfg.wasm_config.eth_implicit_accounts,
        "eth_wallet_global_contract_hash": {
            "mainnet": near_wallet_contract::eth_wallet_global_contract_hash("mainnet").to_string(),
            "testnet": near_wallet_contract::eth_wallet_global_contract_hash("testnet").to_string(),
            "other(arena-v3-local)": near_wallet_contract::eth_wallet_global_contract_hash("arena-v3-local").to_string(),
            "other_hex": hex::encode(near_wallet_contract::eth_wallet_global_contract_hash("arena-v3-local").0),
            "mainnet_hex": hex::encode(near_wallet_contract::eth_wallet_global_contract_hash("mainnet").0),
            "testnet_hex": hex::encode(near_wallet_contract::eth_wallet_global_contract_hash("testnet").0),
        },
        "access_key_min_gas_key_borsh_len": near_primitives::account::AccessKey::min_gas_key_borsh_len(),
        "gas_key_info_borsh_len": near_primitives::account::GasKeyInfo::borsh_len(),
        "gas_key_max_balance_to_burn": near_primitives::account::GasKeyInfo::MAX_BALANCE_TO_BURN.as_yoctonear().to_string(),
        "gas_key_max_nonces": near_primitives::account::AccessKeyPermission::MAX_NONCES_FOR_GAS_KEY,
        "max_account_deletion_storage_usage": near_primitives_core::account::Account::MAX_ACCOUNT_DELETION_STORAGE_USAGE,
        "witness": {"main_storage_proof_size_soft_limit": cfg.witness_config.main_storage_proof_size_soft_limit},
    })
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
    let mut d = d;
    if args.iter().any(|a| a == "--d2") {
        d["d2_runtime"] = d2_params(&cfg);
    }
    if args.iter().any(|a| a == "--d1") {
        // spec/challenge-inputs/runtime-config-pv86-v3-d1.json: plus the fees D1 reads
        d["d1_transaction_fees"] = d1_fees(&cfg);
    }
    std::fs::write(&out, serde_json::to_string_pretty(&d).unwrap()).unwrap();
    0
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = match args.get(1).map(String::as_str) {
        Some("gen") => cmd_gen(&args),
        Some("params") => cmd_params(&args),
        Some("ed25519-judge") => ed25519v::cmd_judge(
            &PathBuf::from(arg(&args, "--in").expect("--in")),
            &PathBuf::from(arg(&args, "--out").expect("--out")),
        ),
        Some("ed25519-sign") => ed25519v::cmd_sign(
            arg(&args, "--seed").and_then(|s| s.parse().ok()).unwrap_or(1),
            arg(&args, "--n").and_then(|s| s.parse().ok()).unwrap_or(1000),
            &PathBuf::from(arg(&args, "--out").expect("--out")),
        ),
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
