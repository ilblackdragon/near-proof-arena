//! near-arena-oracle-v3-successor: domain-D3 oracle for `near/pv86/chunk-validation/v0` (README.md).
//!
//! Commands:
//!   gen --domain d3 --seed S --out DIR [--first-chain I] [--chains K] [--blocks N]
//!       [--mutate-every M] [--ood-cap C] [--drop-cap D] [--p-missing P] [--max-d3 X]
//!       [--code-mutant-p Q]   (full mutant set every M-th D3 case; code mutants only for a
//!                              fraction Q of the other D3 cases with code blobs)
//!       [--min-gas-price P]   (genesis min_gas_price in yoctoNEAR; default 0 = zero gas price)
//!       Real multi-shard nearcore TestEnv chains with the D2 workload plus WASM FunctionCall
//!       traffic (src/d3gen.rs). Every honest chunk witness: DIR/d3/<case> (in D3α) or
//!       DIR/ood/<case> (out of D3α, capped per violation family), with claim.bin,
//!       witness.bin = encode_witness(ChunkStateWitness, needed codes) and meta.json (verdict
//!       of a cold nearcore validator, D0–D3 classification, executed contracts, features);
//!       mutants of D3 cases in DIR/mutants/<case>-<mutation>; DIR/summary.json.
//!       Chain i uses chain_params_d3(seed, i) (shards 4/5/6, Reed–Solomon seats, gas limits,
//!       epoch lengths as the D2 generator).
//!       Arena (judge) layout: --fixtures-layout [--class d3-maxgas|d3-callbacks|d3-calls|d3-nonwasm]
//!       [--d0-target N] [--rejection-target R] [--no-positives] [--accepted-mutants]
//!       [--per-chain-cap K] runs the above into DIR/.raw and converts it to DIR/cases/<n>/
//!       {request,witness,expected_claim}.bin + DIR/rejections/<n>/ (../v3-d1/src/arena.rs).
//!   arena-layout --domain d3 --in RAW --out DIR [arena options]
//!       The same conversion of an existing corpus (public fixtures).
//!   contracts
//!       Print the code registry (name, hash, length, D3α facts).
//!   mldsa-vectors
//!       Print ML-DSA-65 verify verdicts of the pinned crate (src/mldsa_vectors.rs) as JSON.
//!   curve-steps
//!       Print the curve-hosts scenario steps (label, method, args, gas) and contract hash as JSON.
//!   mainnet-observables --home HOME --exports EXPORTS --cases CASES --out FILE
//!       nearcore's stored outcomes, outgoing receipts and state changes of each captured mainnet
//!       witness's main transition, from a stopped node's database opened read-only
//!       (src/mainnet_obs.rs, workplan W01).
//!   rejudge-d2 --corpus D2CORPUS --cases LIST --chain I --blocks N --out OUT --scratch SCRATCH
//!       Cold re-judgment of existing d2corpus.v2 cases with the needed code blobs appended
//!       (src/d2cold.rs): replays the D2 chain byte-identically and writes OUT/<sub>/<case>.
//!   observe-d1 | observe-d2 --corpus DIR --chain I --out OUT --scratch SCRATCH
//!       nearcore's per-outcome observables (cold validator) for the pinned d1run / d2corpus.v2
//!       cases of chain I, by re-running the original D1/D2 generator chain unchanged with an
//!       observation hook on its judge (src/d12obs.rs, workplan W01).
//!   reshard --seed S --out DIR [--chains K] [--first-chain I] [--blocks N] [--shards n]
//!       [--epoch-length L] [--gas-limit-tgas G] [--split-k k] [--variant v] [--p-missing P]
//!       [--p-burst-hot B] [--min-gas-price P] [--second-split SID] [--max-shards M] [--no-force]
//!       [--mem-threshold T] [--min-child C] [--starve SID:EPOCHS] [--zlim] [--p-global-hot P]
//!       Real shard-split chains (src/reshard.rs, workplan W11): PV85 genesis, PV86 dynamic
//!       resharding forcing a split of the shard of `s{k}a00`; every witness in DIR/cases/<case>,
//!       split/layout mutants in DIR/mutants/<case>-<mutation>, DIR/summary.json.

// Shared, unmodified, with the D0 oracle (oracle/v3/src, pinned by the signed D0 challenge).
#[path = "../../v3/src/claim.rs"]
mod claim;
#[path = "../../v3/src/d0.rs"]
mod d0;
#[path = "../../v3/src/enc.rs"]
mod enc;
// `judge` is the shared module plus an observation hook that no command but `observe-d1/d2`
// installs (src/judge_hook.rs re-exports `../../v3/src/judge.rs` unchanged).
#[path = "judge_hook.rs"]
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
#[path = "../../v3-d1/src/arena.rs"]
mod arena;
// D3 (this crate). `chaind3.rs` is a versioned copy of the signed loop with scenario hooks.
mod chaind3;
mod keys;
mod scenarios;
mod xfam;
mod rterr;
mod d3;
mod d3contracts;
mod d3gen;
mod codec_probe;
mod curve_hosts;
mod mldsa_vectors;
mod reshard;
mod observables;
mod mainnet_obs;
mod d2cold;
mod cachejudge;
mod d12obs;
mod l0mut;
#[path = "../../v3-d3/src/d3judge.rs"]
mod d3judge;

use serde_json::json;
use std::path::PathBuf;

const NEARCORE_COMMIT: &str = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993";

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

/// D3 chain parameters of chain `i` (the D2 generator's parameter rotation).
/// `long_skip`: `--long-skip START:LEN:K` overrides the rotation's long run of missing chunks
/// (rounds `START..START+LEN` skip the chunk of the shard of account group `K`) on every chain;
/// absent, the rotation is unchanged.
fn chain_params_d3(seed: u64, i: usize, blocks: u64, p_missing: f64, drop_cap: usize, max_d3: usize, code_mutant_p: f64, min_gas_price: u128, long_skip: Option<(u64, u64, usize)>) -> chaind3::D3Params {
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
            long_skip: long_skip.or(if i % 8 == 5 { Some((60, 40, 0)) } else { None }),
        },
        max_txs: 4,
        p_contract: 0.04,
        // quiet scenarios (storage-limits) run only their own transactions: no crafted injections
        p_adv: if scenarios::quiet() { 0.0 } else { 0.3 },
        drop_cap,
        max_d3,
        code_mutant_p,
        min_gas_price,
    }
}

fn cmd_gen(args: &[String]) -> i32 {
    if arg(args, "--domain").as_deref() != Some("d3") {
        eprintln!("near-arena-oracle-v3-successor generates domain D3 only (--domain d3)");
        return 2;
    }
    // arena (judge) layout: the difftest-layout run into OUT/.raw, then `arena::convert`
    if args.iter().any(|a| a == "--fixtures-layout") {
        return arena::gen_fixtures(args, "d3", |raw| cmd_gen(&arena::raw_args(args, raw)));
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
    let min_gas_price: u128 = arg(args, "--min-gas-price").map(|s| s.parse().expect("--min-gas-price")).unwrap_or(0);
    let long_skip: Option<(u64, u64, usize)> = arg(args, "--long-skip").map(|s| {
        let v: Vec<&str> = s.split(':').collect();
        assert_eq!(v.len(), 3, "--long-skip START:LEN:K");
        (v[0].parse().expect("--long-skip START"), v[1].parse().expect("--long-skip LEN"), v[2].parse().expect("--long-skip K"))
    });
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
        let p = chain_params_d3(seed, i, blocks, p_missing, drop_cap, max_d3, code_mutant_p, min_gas_price, long_skip);
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
        Some("codec-roundtrip") => codec_probe::command(&args),
        Some("curve-steps") => curve_hosts::print_steps(),
        Some("mldsa-vectors") => mldsa_vectors::command(&args),
        Some("reshard") => reshard::cmd_reshard(&args),
        Some("mainnet-observables") => mainnet_obs::cmd(&args),
        Some("rejudge-d2") => d2cold::cmd(&args),
        Some("observe-d1") => d12obs::cmd(&args, true),
        Some("observe-d2") => d12obs::cmd(&args, false),
        Some("arena-layout") => arena::cmd_arena_layout(&args),
        _ => {
            eprintln!("usage: near-arena-oracle-v3-successor gen --domain d3 ... | contracts (see src/main.rs)");
            2
        }
    };
    std::process::exit(code);
}
