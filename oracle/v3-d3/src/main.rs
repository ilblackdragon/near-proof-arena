//! near-arena-oracle-v3-d3: domain-D3 oracle for `near/pv86/chunk-validation/v0` (README.md).
//!
//! Commands:
//!   gen --domain d3 --seed S --out DIR [--first-chain I] [--chains K] [--blocks N]
//!       [--mutate-every M] [--ood-cap C] [--drop-cap D] [--p-missing P] [--max-d3 X]
//!       [--code-mutant-p Q]   (full mutant set every M-th D3 case; code mutants only for a
//!                              fraction Q of the other D3 cases with code blobs)
//!       Real multi-shard nearcore TestEnv chains with the D2 workload plus WASM FunctionCall
//!       traffic (src/d3gen.rs). Every honest chunk witness: DIR/d3/<case> (in D3α) or
//!       DIR/ood/<case> (out of D3α, capped per violation family), with claim.bin,
//!       witness.bin = encode_witness(ChunkStateWitness, needed codes) and meta.json (verdict
//!       of a cold nearcore validator, D0–D3 classification, executed contracts, features);
//!       mutants of D3 cases in DIR/mutants/<case>-<mutation>; DIR/summary.json.
//!       Chain i uses chain_params_d3(seed, i) (shards 4/5/6, Reed–Solomon seats, gas limits,
//!       epoch lengths as the D2 generator).
//!   contracts
//!       Print the code registry (name, hash, length, D3α facts).

// Shared, unmodified, with the D0 oracle (oracle/v3/src, pinned by the signed D0 challenge).
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
// Shared, unmodified, with the D1/D2 oracle (oracle/v3-d1/src).
#[allow(dead_code)]
#[path = "../../v3-d1/src/chaingen.rs"]
mod chaingen;
#[allow(dead_code)]
#[path = "../../v3-d1/src/chaind2.rs"]
mod chaind2;
#[allow(dead_code)]
#[path = "../../v3-d1/src/d1.rs"]
mod d1;
#[allow(dead_code)]
#[path = "../../v3-d1/src/d1gen.rs"]
mod d1gen;
#[allow(dead_code)]
#[path = "../../v3-d1/src/d1judge.rs"]
mod d1judge;
#[allow(dead_code)]
#[path = "../../v3-d1/src/d2.rs"]
mod d2;
#[allow(dead_code)]
#[path = "../../v3-d1/src/d2gen.rs"]
mod d2gen;
// D3 (this crate)
mod chaind3;
mod d3;
mod d3contracts;
mod d3gen;
mod d3judge;

use serde_json::json;
use std::path::PathBuf;

const NEARCORE_COMMIT: &str = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993";

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

/// D3 chain parameters of chain `i` (the D2 generator's parameter rotation).
fn chain_params_d3(seed: u64, i: usize, blocks: u64, p_missing: f64, drop_cap: usize, max_d3: usize, code_mutant_p: f64) -> chaind3::D3Params {
    chaind3::D3Params {
        base: chaingen::ChainParams {
            seed: seed.wrapping_mul(1_000_003).wrapping_add(i as u64),
            n_shards: [4usize, 5, 6][i % 3],
            seats: [8u64, 100, 16, 3][i % 4],
            gas_limit_tgas: [1000u64, 1000, 1000, 10, 60][i % 5],
            epoch_length: [30u64, 20, 12][(i / 3) % 3],
            blocks,
            p_missing,
            p_tx_shard: 0.5,
            p_burst: 0.03,
            p_fail: 0.0,
            p_implicit: 0.0,
            p_two: 0.0,
            long_skip: if i % 8 == 5 { Some((60, 40, 0)) } else { None },
        },
        max_txs: 4,
        p_contract: 0.04,
        p_adv: 0.3,
        drop_cap,
        max_d3,
        code_mutant_p,
    }
}

fn cmd_gen(args: &[String]) -> i32 {
    if arg(args, "--domain").as_deref() != Some("d3") {
        eprintln!("near-arena-oracle-v3-d3 generates domain D3 only (--domain d3)");
        return 2;
    }
    let num = |n: &str, d: u64| -> u64 { arg(args, n).map(|v| v.parse().unwrap_or_else(|_| panic!("{n}: not a number"))).unwrap_or(d) };
    let seed = num("--seed", 7);
    let out = PathBuf::from(arg(args, "--out").expect("--out"));
    let chains = num("--chains", 1) as usize;
    let first = num("--first-chain", 0) as usize;
    let blocks = num("--blocks", 120);
    let p_missing: f64 = arg(args, "--p-missing").map(|s| s.parse().expect("--p-missing")).unwrap_or(0.1);
    let drop_cap = num("--drop-cap", 48) as usize;
    let max_d3 = num("--max-d3", 4) as usize;
    let code_mutant_p: f64 = arg(args, "--code-mutant-p").map(|s| s.parse().expect("--code-mutant-p")).unwrap_or(0.25);
    let opts = chaingen::GenOpts {
        ood_cap: num("--ood-cap", 25) as usize,
        mutate_every: num("--mutate-every", 20) as usize,
        fixtures_layout: false,
        class: chaingen::CaseClass::Any,
        no_positives: false,
        accepted_mutants: false,
        positive_target: 0,
        rejection_target: 0,
        per_chain_cap: 0,
        d1: false,
        p_adv: 0.3,
    };
    std::fs::create_dir_all(&out).unwrap();
    let mut stats = chaingen::Stats {
        honest: 0, honest_ok: 0, d0: 0, ood_written: 0, mutants: 0, by_violation: Default::default(),
        positives: 0, rejections: 0, d1: 0, injected: 0,
    };
    let mut d3s = d3::D3Stats::default();
    let mut params = Vec::new();
    for i in first..first + chains {
        let p = chain_params_d3(seed, i, blocks, p_missing, drop_cap, max_d3, code_mutant_p);
        let pstr = format!("{p:?}");
        eprintln!("chain {i}: {pstr}");
        params.push(pstr);
        chaind3::run_chain_d3(i, &p, &out, &opts, &mut stats, &mut d3s);
        eprintln!(
            "  honest={} cold_ok={} d3={} d1={} d0={} ood_written={} mutants={} crafted={}",
            stats.honest, stats.honest_ok, stats.positives, stats.d1, stats.d0, stats.ood_written, stats.mutants, stats.injected
        );
    }
    let summary = json!({
        "nearcore_commit": NEARCORE_COMMIT, "protocol_version": 86, "seed": seed, "domain": "D3alpha",
        "chains": params, "honest_witnesses": stats.honest, "honest_accepted_by_nearcore": stats.honest_ok,
        "d3_cases": stats.positives, "d1_cases_among_d3": stats.d1, "d0_cases_among_d3": stats.d0,
        "ood_cases_written": stats.ood_written, "mutants": stats.mutants,
        "crafted_transactions": stats.injected, "d3_violation_counts": stats.by_violation,
        "d3": d3s.counters,
    });
    std::fs::write(out.join("summary.json"), serde_json::to_string_pretty(&summary).unwrap()).unwrap();
    if stats.honest_ok != stats.honest {
        eprintln!("WARNING: some honest witnesses were rejected by the cold validator");
        return 1;
    }
    0
}

fn cmd_contracts() -> i32 {
    for (h, (n, c)) in &d3contracts::registry().by_hash {
        let f = d3contracts::code_facts(c);
        println!(
            "{n:10} {h} {:6} float={} curve={:?} ed25519={} chain_id={} parse_error={}",
            c.len(),
            f.float,
            f.curve_imports,
            f.ed25519_import,
            f.chain_id_import,
            f.parse_error
        );
    }
    0
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let code = match args.get(1).map(String::as_str) {
        Some("gen") => cmd_gen(&args),
        Some("contracts") => cmd_contracts(),
        _ => {
            eprintln!("usage: near-arena-oracle-v3-d3 gen --domain d3 ... | contracts (see src/main.rs)");
            2
        }
    };
    std::process::exit(code);
}
