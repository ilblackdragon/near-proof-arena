//! `observe-d1` / `observe-d2` (workplan W01): nearcore's per-outcome observables for the pinned
//! `d1run` and `d2corpus.v2` corpora, which the D1/D2 generator (oracle/v3-d1) wrote without them.
//!
//! The command re-runs one chain of the original generator *unchanged* (`chaingen::run_chain` for
//! D1, `chaind2::run_chain_d2` for D2, the shared oracle/v3-d1 sources compiled into this crate),
//! with the original parameters (`oracle/scripts/regen-fixtures-v3.sh:38`, `gen-d2-corpus.sh`),
//! into a scratch directory. The generator judges every honest witness it captures with
//! `judge::nearcore_judge`; this crate's `judge` is the shared module plus an observation hook
//! (`judge_hook.rs`). The hook looks up the judged state-witness bytes among the corpus cases of
//! the chain (by sha256 of the Borsh `ChunkStateWitness`, the bytes inside the corpus
//! `witness.bin`), and for a hit runs `observables::observe` with a *cold* validator runtime (its
//! own `NightshadeRuntime` over the client's store, empty compiled-contract cache) and the code
//! blobs the corpus `witness.bin` carries. The record is bound to the corpus case by the sha256 of
//! its `claim.bin` and `witness.bin` (as `observables::Collector` records are), so the comparator
//! needs no names.
//!
//! A corpus case that the replay never produces is listed in `missing` (the replay is not
//! byte-identical there); the command fails unless every case of the chain is found.
//!
//! usage: observe-d1 --corpus D1RUN --chain I --out OUT --scratch SCRATCH
//!        observe-d2 --corpus D2CORPUS --chain I --out OUT --scratch SCRATCH
//!        [--seed S] [--blocks N] [--ood-cap C] [--mutate-every M] [--drop-cap D] [--p-missing P]

use crate::chaingen::{ChainParams, GenOpts, Stats};
use crate::d3judge::ColdCache;
use near_chain::ChainStoreAccess;
use near_chain::runtime::NightshadeRuntime;
use near_chain_configs::Genesis;
use near_client::Client;
use near_epoch_manager::{EpochManager, EpochManagerHandle};
use near_parameters::RuntimeConfigStore;
use near_primitives::epoch_manager::{EpochConfig, EpochConfigStore};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

fn sha(b: &[u8]) -> String {
    hex::encode(Sha256::digest(b))
}

/// `oracle/v3-d1/src/main.rs` `chain_params` (D1), unchanged.
fn chain_params_d1(seed: u64, i: usize, blocks: u64, p_missing: f64) -> ChainParams {
    let seats = [8u64, 100, 16, 3][i % 4];
    ChainParams {
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

/// `oracle/v3-d1/src/main.rs` `chain_params_d2`, unchanged.
fn chain_params_d2(seed: u64, i: usize, blocks: u64, p_missing: f64, keep_every: u64, drop_cap: usize) -> crate::chaind2::D2Params {
    crate::chaind2::D2Params {
        base: ChainParams {
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
            long_skip: if i % 8 == 5 { Some((60, 40, 0)) } else { None },
        },
        max_txs: 6,
        p_contract: if blocks >= 250 { 0.10 } else { 0.04 },
        p_adv: 0.35,
        keep_every,
        drop_cap,
    }
}

/// Corpus `witness.bin` = bytes(tag) ‖ bytes(state witness) ‖ u32 n ‖ n × bytes(code), each
/// `bytes` a u32-length-prefixed string (`enc.rs` `encode_witness`).
fn split_witness_file(b: &[u8]) -> Option<(Vec<u8>, Vec<Vec<u8>>)> {
    let u32at = |o: usize| -> Option<usize> { Some(u32::from_le_bytes(b.get(o..o + 4)?.try_into().ok()?) as usize) };
    let n = u32at(0)?;
    let o = 4 + n;
    let n = u32at(o)?;
    let sw = b.get(o + 4..o + 4 + n)?.to_vec();
    let mut o = o + 4 + n;
    let k = u32at(o)?;
    o += 4;
    let mut codes = Vec::new();
    for _ in 0..k {
        let n = u32at(o)?;
        codes.push(b.get(o + 4..o + 4 + n)?.to_vec());
        o += 4 + n;
    }
    (o == b.len()).then_some((sw, codes))
}

struct Want {
    case: String,
    claim_sha: String,
    witness_sha: String,
    codes: Vec<Vec<u8>>,
}

/// Every corpus case of chain `chain` under `subs`, keyed by sha256(state witness bytes).
fn wanted(corpus: &Path, subs: &[&str], chain: usize) -> HashMap<String, Want> {
    let mut m = HashMap::new();
    for sub in subs {
        let Ok(rd) = std::fs::read_dir(corpus.join(sub)) else { continue };
        let mut names: Vec<String> = rd.filter_map(|e| e.ok()?.file_name().into_string().ok()).collect();
        names.sort();
        for name in names {
            if !name.starts_with(&format!("{chain:02}-")) {
                continue;
            }
            let d = corpus.join(sub).join(&name);
            let w = std::fs::read(d.join("witness.bin")).unwrap();
            let c = std::fs::read(d.join("claim.bin")).unwrap();
            let (sw, codes) = split_witness_file(&w).unwrap_or_else(|| panic!("{}: witness.bin layout", d.display()));
            m.insert(sha(&sw), Want { case: format!("{sub}/{name}"), claim_sha: sha(&c), witness_sha: sha(&w), codes });
        }
    }
    m
}

/// A cold validator runtime over `client`'s store: empty compiled-contract cache, its own epoch
/// manager handle over the same store, the chain's genesis config (as `observables::Collector`).
fn cold_runtime(client: &Client, genesis: &Genesis, home: &Path) -> (Arc<NightshadeRuntime>, ColdCache) {
    let store = client.chain.chain_store().store();
    let mut base: EpochConfig = (&genesis.config).into();
    base.block_producer_kickout_threshold = 0;
    base.chunk_producer_kickout_threshold = 0;
    let ecs = EpochConfigStore::test(BTreeMap::from_iter(vec![(genesis.config.protocol_version, Arc::new(base))]));
    let em: Arc<EpochManagerHandle> = EpochManager::new_arc_handle_from_epoch_config_store(store.clone(), &genesis.config, ecs);
    let cache = ColdCache::default();
    std::fs::create_dir_all(home).unwrap();
    let rt = NightshadeRuntime::test_with_runtime_config_store(home, store, Box::new(cache.clone()), &genesis.config, em, RuntimeConfigStore::new(None));
    (rt, cache)
}

pub fn cmd(args: &[String], d1: bool) -> i32 {
    let corpus = PathBuf::from(arg(args, "--corpus").expect("--corpus"));
    let chain: usize = arg(args, "--chain").expect("--chain").parse().unwrap();
    let out = PathBuf::from(arg(args, "--out").expect("--out"));
    let scratch = PathBuf::from(arg(args, "--scratch").expect("--scratch"));
    let num = |n: &str, d: u64| -> u64 { arg(args, n).map(|v| v.parse().unwrap()).unwrap_or(d) };
    let p_missing: f64 = arg(args, "--p-missing").map(|s| s.parse().unwrap()).unwrap_or(0.12);
    std::fs::create_dir_all(&out).unwrap();
    std::fs::create_dir_all(&scratch).unwrap();
    let mut stats = Stats {
        honest: 0, honest_ok: 0, d0: 0, ood_written: 0, mutants: 0, by_violation: Default::default(),
        positives: 0, rejections: 0, d1: 0, injected: 0,
    };
    // the original generator's options: D1 `regen-fixtures-v3.sh:38`, D2 `gen-d2-corpus.sh`
    let (seed, blocks, opts, subs): (u64, u64, GenOpts, Vec<&str>) = if d1 {
        let opts = GenOpts {
            ood_cap: num("--ood-cap", 40) as usize, mutate_every: num("--mutate-every", 4) as usize,
            fixtures_layout: false, class: crate::chaingen::CaseClass::Any, no_positives: false,
            accepted_mutants: false, positive_target: 0, rejection_target: 0, per_chain_cap: 0, d1: true, p_adv: 0.5,
        };
        (num("--seed", 5151), num("--blocks", 150), opts, vec!["d1", "ood"])
    } else {
        let blocks = num("--blocks", if [2, 7, 12].contains(&chain) { 270 } else { 200 });
        let opts = GenOpts {
            ood_cap: num("--ood-cap", 15) as usize, mutate_every: num("--mutate-every", 14) as usize,
            fixtures_layout: false, class: crate::chaingen::CaseClass::Any, no_positives: false,
            accepted_mutants: false, positive_target: 0, rejection_target: 0, per_chain_cap: 0, d1: false, p_adv: 0.35,
        };
        (num("--seed", 6262), blocks, opts, vec!["d2", "ood"])
    };
    let want = wanted(&corpus, &subs, chain);
    eprintln!("chain {chain}: {} corpus cases to observe", want.len());
    let (params, genesis) = if d1 {
        let p = chain_params_d1(seed, chain, blocks, p_missing);
        let g = crate::chaingen::setup_with(&p, true).genesis;
        (Params::D1(p), g)
    } else {
        let dp = chain_params_d2(seed, chain, blocks, p_missing, 1, num("--drop-cap", 96) as usize);
        let g = crate::chaind2::setup_d2(&dp.base).genesis;
        (Params::D2(dp), g)
    };
    let file = std::fs::File::create(out.join(format!("nearcore-observables-{chain:02}.jsonl"))).unwrap();
    let state = Rc::new(RefCell::new(HookState {
        want,
        seen: BTreeMap::new(),
        rts: HashMap::new(),
        genesis,
        home: scratch.join(format!(".obs-{chain}")),
        file: std::io::BufWriter::new(file),
        chain,
        judged: 0,
    }));
    let st = state.clone();
    crate::judge::set_hook(Some(Box::new(move |client: &Client, bytes: &[u8], _codes: &[Vec<u8>]| {
        st.borrow_mut().on_judge(client, bytes);
    })));
    let raw = scratch.join(format!("chain-{chain}"));
    match &params {
        Params::D1(p) => crate::chaingen::run_chain(chain, p, &raw, &opts, &mut stats),
        Params::D2(dp) => crate::chaind2::run_chain_d2(chain, dp, &raw, &opts, &mut stats),
    }
    crate::judge::set_hook(None);
    let mut s = state.borrow_mut();
    s.file.flush().unwrap();
    let missing: Vec<String> = s.want.iter().filter(|(k, _)| !s.seen.contains_key(*k)).map(|(_, w)| w.case.clone()).collect();
    let summary = json!({
        "chain": chain, "domain": if d1 { "D1" } else { "D2" }, "params": format!("{params:?}"),
        "corpus": corpus.display().to_string(), "corpus_cases": s.want.len(), "observed": s.seen.len(),
        "statuses": s.seen.values().fold(BTreeMap::<String, usize>::new(), |mut m, v| { *m.entry(v.clone()).or_default() += 1; m }),
        "missing": missing, "honest_regenerated": stats.honest, "honest_ok": stats.honest_ok,
        "judge_calls": s.judged,
    });
    std::fs::write(out.join(format!("observe-{chain:02}.json")), serde_json::to_string_pretty(&summary).unwrap()).unwrap();
    if !missing.is_empty() {
        eprintln!("chain {chain}: {} corpus cases not regenerated", missing.len());
        return 1;
    }
    0
}

#[derive(Debug)]
enum Params {
    D1(ChainParams),
    D2(crate::chaind2::D2Params),
}

use std::cell::RefCell;
use std::rc::Rc;

struct HookState {
    want: HashMap<String, Want>,
    seen: BTreeMap<String, String>,
    rts: HashMap<usize, (Arc<NightshadeRuntime>, ColdCache)>,
    genesis: Genesis,
    home: PathBuf,
    file: std::io::BufWriter<std::fs::File>,
    chain: usize,
    judged: usize,
}

impl HookState {
    fn on_judge(&mut self, client: &Client, bytes: &[u8]) {
        self.judged += 1;
        let key = sha(bytes);
        if self.seen.contains_key(&key) {
            return;
        }
        let Some(w) = self.want.get(&key) else { return };
        let id = client as *const Client as usize;
        if !self.rts.contains_key(&id) {
            let home = self.home.join(format!("rt-{}", self.rts.len()));
            let rt = cold_runtime(client, &self.genesis, &home);
            self.rts.insert(id, rt);
        }
        let (rt, cache) = &self.rts[&id];
        cache.clear();
        let codes = w.codes.clone();
        let body = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| crate::observables::observe(client, rt.as_ref(), bytes, &codes))) {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => json!({ "status": format!("error: {e}") }),
            Err(_) => json!({ "status": "error: panic" }),
        };
        cache.clear();
        let status = body.get("status").and_then(Value::as_str).unwrap_or("?").split(':').next().unwrap_or("?").to_string();
        let mut rec = json!({
            "chain": self.chain, "case": w.case, "claim_sha256": w.claim_sha, "witness_sha256": w.witness_sha,
            "state_witness_sha256": key, "codes": w.codes.len(),
        });
        if let (Value::Object(m), Value::Object(b)) = (&mut rec, body) {
            m.extend(b);
        }
        writeln!(self.file, "{}", serde_json::to_string(&rec).unwrap()).unwrap();
        self.seen.insert(key, status);
    }
}
