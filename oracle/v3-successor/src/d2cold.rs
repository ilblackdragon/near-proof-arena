//! `rejudge-d2`: a cold re-judgment of existing domain-D2 corpus cases (`d2corpus.v2`).
//!
//! The D2 generator (oracle/v3-d1, `gen --domain d2`) judged every honest witness with the
//! TestEnv client's own, warm, validator and wrote `witness.bin` with no code blobs
//! (`d2.rs` `write_case`: `encode_witness(witness, &[])`). A chunk that calls a pre-state
//! contract (the `s{k}ct` program contract, a `small_wasm` deployed earlier) is therefore labelled
//! `nearcore: ok` from a validator whose compiled-contract cache already holds the code, while a
//! cold validator given those bytes reports `MissingTrieValue` (README.md "How a stateless
//! validator obtains contract code").
//!
//! This command replays the D2 chain loop (`chaind2::run_chain_d2`, reproduced here verbatim
//! apart from the capture of nearcore's contract accesses and the extra judgments, so the RNG
//! stream and therefore every witness are byte-identical) and, for each selected case,
//!   * checks that the regenerated `ChunkStateWitness` and claim equal the corpus bytes,
//!   * judges it with the cold validator (`d3judge::ColdJudge`) without and with the needed code
//!     blobs (nearcore's `contract_accesses`, bytes from the D2 code registry),
//!   * writes `OUT/<case>/{claim.bin, witness.bin (with the codes), meta.json}`, the corpus
//!     `meta.json` with the cold verdict in `nearcore` and the warm one kept as
//!     `nearcore_warm_no_codes`.
//! The corpus output of the replay itself (`write_d2_case`, which consumes the RNG) goes to
//! `SCRATCH` and is not used.
//!
//! usage: rejudge-d2 --corpus D2CORPUS --cases LIST --chain I --blocks N --out OUT --scratch SCRATCH
//!        [--seed 6262] [--ood-cap 15] [--mutate-every 14] [--drop-cap 96] [--p-missing 0.12]

use crate::chaind2::{D2Params, setup_d2, stakers_of, validators_of};
use crate::chaingen::{ChainParams, GenOpts, Setup, Stats};
use crate::claim::build_claim;
use crate::judge::nearcore_judge;
use near_chain::Provenance;
use near_chain::chain::ChunkStateWitnessMessage;
use near_chain::stateless_validation::processing_tracker::ProcessingDoneTracker;
use near_crypto::InMemorySigner;
use near_parameters::RuntimeConfigStore;
use near_primitives::action::{Action, TransferAction};
use near_primitives::hash::CryptoHash;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::transaction::SignedTransaction;
use near_primitives::types::{AccountId, Balance};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde_json::json;
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

const ACCTS_PER_SHARD: usize = 10;

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

/// `oracle/v3-d1/src/main.rs` `chain_params_d2`, unchanged.
fn chain_params_d2(seed: u64, i: usize, blocks: u64, p_missing: f64, keep_every: u64, drop_cap: usize) -> D2Params {
    D2Params {
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

/// The D2 code registry: every contract the D2 workload deploys or calls (`d2gen.rs`).
fn d2_codes() -> HashMap<CryptoHash, (String, Vec<u8>)> {
    let mut m = HashMap::new();
    m.insert(CryptoHash::hash_bytes(crate::d2gen::program_wasm()), ("program".to_string(), crate::d2gen::program_wasm().to_vec()));
    for i in 0..4 {
        let c = crate::d2gen::small_wasm(i);
        m.entry(CryptoHash::hash_bytes(&c)).or_insert((format!("small_wasm({i})"), c));
    }
    m
}

/// Corpus `witness.bin` = tag ‖ bytes(state_witness) ‖ u32 n ‖ n × bytes(code) (enc.rs).
fn split_witness_file(b: &[u8]) -> Option<(Vec<u8>, usize)> {
    let rd = |o: usize| -> Option<(usize, usize)> {
        let n = u32::from_le_bytes(b.get(o..o + 4)?.try_into().ok()?) as usize;
        Some((o + 4, n))
    };
    let (o, n) = rd(0)?;
    let o = o + n; // tag
    let (o, n) = rd(o)?;
    let sw = b.get(o..o + n)?.to_vec();
    let (_, k) = rd(o + n)?;
    Some((sw, k))
}

fn vstr(r: &Result<(), String>) -> String {
    r.as_ref().map(|_| "ok".to_string()).unwrap_or_else(|e| e.clone())
}

pub fn cmd(args: &[String]) -> i32 {
    let corpus = PathBuf::from(arg(args, "--corpus").expect("--corpus"));
    let list = arg(args, "--cases").expect("--cases");
    let chain: usize = arg(args, "--chain").expect("--chain").parse().unwrap();
    let blocks: u64 = arg(args, "--blocks").expect("--blocks").parse().unwrap();
    let out = PathBuf::from(arg(args, "--out").expect("--out"));
    let scratch = PathBuf::from(arg(args, "--scratch").expect("--scratch"));
    let seed: u64 = arg(args, "--seed").map(|s| s.parse().unwrap()).unwrap_or(6262);
    let ood_cap: usize = arg(args, "--ood-cap").map(|s| s.parse().unwrap()).unwrap_or(15);
    let mutate_every: usize = arg(args, "--mutate-every").map(|s| s.parse().unwrap()).unwrap_or(14);
    let drop_cap: usize = arg(args, "--drop-cap").map(|s| s.parse().unwrap()).unwrap_or(96);
    let p_missing: f64 = arg(args, "--p-missing").map(|s| s.parse().unwrap()).unwrap_or(0.12);
    // selected cases: lines "<sub>/<case>" (e.g. `ood/03-h10021-s2`) whose case starts with the chain
    let want: BTreeMap<String, String> = std::fs::read_to_string(&list)
        .unwrap()
        .lines()
        .filter_map(|l| {
            let l = l.trim();
            let (sub, case) = l.rsplit_once('/')?;
            let sub = sub.rsplit('/').next()?;
            case.starts_with(&format!("{chain:02}-")).then(|| (case.to_string(), sub.to_string()))
        })
        .collect();
    eprintln!("chain {chain}: {} selected cases", want.len());
    let opts = GenOpts {
        ood_cap,
        mutate_every,
        fixtures_layout: false,
        class: crate::chaingen::CaseClass::Any,
        no_positives: false,
        accepted_mutants: false,
        positive_target: 0,
        rejection_target: 0,
        per_chain_cap: 0,
        d1: false,
        p_adv: 0.35,
    };
    let dp = chain_params_d2(seed, chain, blocks, p_missing, 1, drop_cap);
    std::fs::create_dir_all(&out).unwrap();
    std::fs::create_dir_all(&scratch).unwrap();
    let mut stats = Stats {
        honest: 0, honest_ok: 0, d0: 0, ood_written: 0, mutants: 0, by_violation: Default::default(),
        positives: 0, rejections: 0, d1: 0, injected: 0,
    };
    let rows = run_chain(chain, &dp, &scratch, &opts, &mut stats, &corpus, &want, &out);
    let summary = json!({
        "chain": chain, "params": format!("{dp:?}"), "selected": want.len(), "found": rows.len(),
        "honest_regenerated": stats.honest, "honest_warm_ok": stats.honest_ok, "rows": rows,
    });
    std::fs::write(out.join(format!("rejudge-{chain:02}.json")), serde_json::to_string_pretty(&summary).unwrap()).unwrap();
    let bad = rows.iter().filter(|r| r["bytes_equal"] != json!(true)).count();
    if rows.len() != want.len() || bad != 0 {
        eprintln!("chain {chain}: {} of {} found, {bad} byte mismatches", rows.len(), want.len());
        return 1;
    }
    0
}

/// `chaind2::run_chain_d2` with nearcore's contract accesses captured and the selected cases
/// cold-judged. Every RNG draw is in the same order as the original.
#[allow(clippy::too_many_arguments)]
fn run_chain(
    chain_idx: usize, dp: &D2Params, scratch: &Path, o: &GenOpts, stats: &mut Stats, corpus: &Path,
    want: &BTreeMap<String, String>, out: &Path,
) -> Vec<serde_json::Value> {
    let p = &dp.base;
    let mut s = setup_d2(p);
    let cold_home = scratch.join(format!(".cold-{chain_idx}"));
    let judge = crate::d3judge::ColdJudge::new(&s.env.clients, &s.ems, &s.genesis, &cold_home);
    let reg = d2_codes();
    let mut rows = Vec::new();
    let mut world = crate::d2gen::World::new(&s.accounts, validators_of(p.n_shards), stakers_of());
    let mut labels: HashMap<CryptoHash, String> = HashMap::new();
    let mut rng = StdRng::seed_from_u64(p.seed);
    let mut ood_count: BTreeMap<String, usize> = BTreeMap::new();
    let mut d2_seen = 0usize;
    let mut seen_cov: std::collections::HashSet<String> = Default::default();
    let mut pending_skips: HashMap<u64, Vec<AccountId>> = HashMap::new();
    let tip0 = s.env.clients[0].chain.head().unwrap();
    let mut height = tip0.height;
    let last_wanted: Option<u64> = want.keys().filter_map(|c| c.split("-h").nth(1)?.split('-').next()?.parse().ok()).max();
    for round in 0..p.blocks {
        height += 1;
        if last_wanted.is_some_and(|h| height > h + 2) {
            break;
        }
        s.clock.advance(near_time::Duration::milliseconds(1100));
        let tip = s.env.clients[0].chain.head().unwrap();
        {
            let em = s.ems[0].read();
            world.minimum_stake = em.minimum_stake(&tip.last_block_hash).map(|b| b.as_yoctonear()).unwrap_or(0);
        }
        let mut txs: Vec<(String, SignedTransaction)> = Vec::new();
        for k in 0..p.n_shards {
            if !rng.gen_bool(p.p_tx_shard) {
                continue;
            }
            if rng.gen_bool(p.p_burst) {
                let n = rng.gen_range(300..700);
                let tgt = (k + rng.gen_range(1..p.n_shards)) % p.n_shards;
                if rng.gen_bool(0.7) {
                    let layout = s.env.clients[0]
                        .epoch_manager
                        .get_shard_layout(&s.env.clients[0].epoch_manager.get_epoch_id_from_prev_block(&tip.last_block_hash).unwrap())
                        .unwrap();
                    let sid = layout.account_id_to_shard_id(&s.accounts[tgt][0]);
                    for off in 2..=4u64 {
                        let a = s.env.get_chunk_producer_at_offset(&tip, off, sid);
                        pending_skips.entry(tip.height + off).or_default().push(a);
                    }
                }
                for _ in 0..n {
                    let signer_id = s.accounts[k][rng.gen_range(0..crate::d2gen::HONEST)].clone();
                    let r = s.accounts[tgt][rng.gen_range(0..crate::d2gen::HONEST)].clone();
                    let dep = rng.gen_range(1..10u128.pow(22));
                    let Some(t) = world.plain_tx(&s, &tip.last_block_hash, &signer_id, &r, vec![Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(dep) })]) else { continue };
                    txs.push(("h.burst".into(), t));
                }
            } else {
                let n = rng.gen_range(1..=dp.max_txs);
                let long = p.blocks >= 250;
                world.yield_bias = long && round < 60;
                let pc = if long { if round < 60 { 0.15 } else { 0.01 } } else { dp.p_contract };
                txs.extend(world.gen_txs(&s, &tip.last_block_hash, height, &mut rng, n, pc));
            }
        }
        for (l, tx) in txs {
            labels.insert(tx.get_hash(), l);
            for h in &s.env.rpc_handlers {
                let _ = h.process_tx(tx.clone(), false, false);
            }
        }
        let mut force_skip: Vec<AccountId> = pending_skips.remove(&(tip.height + 2)).unwrap_or_default();
        if let Some((start, len, k)) = p.long_skip {
            if round >= start && round < start + len {
                let em = &s.env.clients[0].epoch_manager;
                let layout = em.get_shard_layout(&em.get_epoch_id_from_prev_block(&tip.last_block_hash).unwrap()).unwrap();
                let sid = layout.account_id_to_shard_id(&s.accounts[k][0]);
                force_skip.push(s.env.get_chunk_producer_at_offset(&tip, 2, sid));
            }
        }
        let inject: Option<(usize, AccountId)> = if rng.gen_bool(dp.p_adv) {
            let k = rng.gen_range(0..p.n_shards);
            let em = &s.env.clients[0].epoch_manager;
            let layout = em.get_shard_layout(&em.get_epoch_id_from_prev_block(&tip.last_block_hash).unwrap()).unwrap();
            let sid = layout.account_id_to_shard_id(&s.accounts[k][0]);
            Some((k, s.env.get_chunk_producer_at_offset(&tip, 2, sid)))
        } else {
            None
        };
        let bp = s.env.get_block_producer_at_offset(&tip, height - tip.height);
        assert!(s.env.contains_client(&bp), "block producer {bp} at height {height} has no client");
        let block = s.env.client(&bp).produce_block(height).unwrap().unwrap();
        for i in 0..s.env.clients.len() {
            let skip = force_skip.contains(&s.env.get_client_id(i)) || rng.gen_bool(p.p_missing);
            let injector = !skip && inject.as_ref().is_some_and(|(_, a)| *a == s.env.get_client_id(i));
            let r = if skip || injector {
                s.env.clients[i].process_block_test_no_produce_chunk(block.clone().into(), Provenance::NONE)
            } else {
                s.env.clients[i].process_block_test(block.clone().into(), Provenance::NONE)
            };
            if injector && r.is_ok() {
                let (k, _) = inject.clone().unwrap();
                let Some(crafted) = craft_for_d2(&s, k, &block, height, p, &mut rng) else {
                    crate::d1gen::produce_chunks_with_injection(&mut s.env.clients[i], &block, None, &mut rng);
                    continue;
                };
                stats.injected += crafted.len();
                let sid = {
                    let em = &s.env.clients[i].epoch_manager;
                    let layout = em.get_shard_layout(&em.get_epoch_id_from_prev_block(block.hash()).unwrap()).unwrap();
                    layout.account_id_to_shard_id(&s.accounts[k][0])
                };
                for (class, t) in &crafted {
                    labels.insert(t.get_hash(), class.clone());
                }
                crate::d1gen::produce_chunks_with_injection(
                    &mut s.env.clients[i],
                    &block,
                    Some((sid, crafted.into_iter().map(|x| x.1).collect())),
                    &mut rng,
                );
            }
            match r.map(|_| ()) {
                Ok(_) => {}
                Err(near_chain::Error::ChunksMissing(_)) => {}
                Err(e) => panic!("process_block: {e:?}"),
            }
        }
        for _ in 0..4 {
            s.env.process_partial_encoded_chunks();
            for j in 0..s.env.clients.len() {
                s.env.process_shards_manager_responses_and_finish_processing_blocks(j);
            }
        }
        for c in &s.env.clients {
            assert_eq!(c.chain.head().unwrap().last_block_hash, *block.hash(), "client did not finish block");
        }
        // ---- capture (witness + nearcore's contract accesses) and deliver witnesses
        let mut captured: Vec<(usize, ChunkStateWitness, Vec<CryptoHash>)> = Vec::new();
        let mut waiters = Vec::new();
        let adapters = s.env.partial_witness_adapters.clone();
        for (ci, ad) in adapters.iter().enumerate() {
            while let Some(req) = ad.pop_distribution_request() {
                let sw = req.state_witness;
                let mut acc: Vec<CryptoHash> = req.contract_updates.contract_accesses.iter().map(|h| h.0).collect();
                acc.sort();
                captured.push((ci, sw.clone(), acc));
                let raw = borsh::object_length(&sw).unwrap();
                let key = sw.chunk_production_key();
                let cvs = s.env.clients[ci]
                    .epoch_manager
                    .get_chunk_validator_assignments(&key.epoch_id, key.shard_id, key.height_created)
                    .unwrap()
                    .ordered_chunk_validators();
                for a in cvs {
                    if !s.env.contains_client(&a) {
                        continue;
                    }
                    let idx = s.env.get_client_index(&a);
                    let t = ProcessingDoneTracker::new();
                    waiters.push(t.make_waiter());
                    let _ = s.env.chunk_validation_actors[idx].process_chunk_state_witness_message(ChunkStateWitnessMessage {
                        witness: sw.clone(),
                        raw_witness_size: raw,
                        processing_done_tracker: Some(t),
                    });
                }
            }
        }
        for wt in waiters {
            wt.wait();
        }
        s.env.propagate_chunk_endorsements(true);

        for (ci, sw, accesses) in captured {
            stats.honest += 1;
            let client = &s.env.clients[ci];
            let built = match build_claim(client, &s.ems[0], &s.genesis.config, &sw) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("claim build failed: {e}");
                    continue;
                }
            };
            let wb = borsh::to_vec(&sw).unwrap();
            let rs = (built.claim.rs_data_parts, built.claim.rs_total_parts);
            let verdict = nearcore_judge(client, &wb, &[], rs);
            if verdict.is_ok() {
                stats.honest_ok += 1;
            }
            let key = sw.chunk_production_key();
            let name = format!("{chain_idx:02}-h{}-s{}", key.height_created, key.shard_id);
            if let Some(sub) = want.get(&name) {
                rows.push(rejudge_one(&judge, ci, client, &built.claim.encode(), &wb, &accesses, &reg, rs, &verdict, corpus, sub, &name, out));
            }
            let tracker = (0..s.env.clients.len()).map(|k| &s.env.clients[k]).find(|c| crate::d0::tracks(c, &built)).unwrap_or(client);
            let viol = match crate::d0::classify(tracker, &built, &sw, wb.len(), 0) {
                Ok(v) => v,
                Err(e) => {
                    eprintln!("classify failed: {e}");
                    continue;
                }
            };
            crate::d2::write_d2_case(
                crate::d2::D2Ctx {
                    tracker,
                    client,
                    built: &built,
                    sw: &sw,
                    wb: &wb,
                    verdict: &verdict,
                    viol: &viol,
                    labels: &labels,
                    chain_idx,
                    params: &format!("{dp:?}"),
                    n_shards: p.n_shards,
                    out: scratch,
                    o,
                    rng: &mut rng,
                    ood_count: &mut ood_count,
                    d2_seen: &mut d2_seen,
                    round,
                    keep_every: dp.keep_every,
                    seen_cov: &mut seen_cov,
                    drop_cap: dp.drop_cap,
                },
                stats,
            );
        }
    }
    rows
}

#[allow(clippy::too_many_arguments)]
fn rejudge_one(
    judge: &crate::d3judge::ColdJudge, ci: usize, client: &near_client::Client, claim: &[u8], wb: &[u8],
    accesses: &[CryptoHash], reg: &HashMap<CryptoHash, (String, Vec<u8>)>, rs: (u16, u16),
    warm: &Result<(), String>, corpus: &Path, sub: &str, name: &str, out: &Path,
) -> serde_json::Value {
    let src = corpus.join(sub).join(name);
    let old_w = std::fs::read(src.join("witness.bin")).unwrap();
    let old_c = std::fs::read(src.join("claim.bin")).unwrap();
    let (old_sw, old_codes) = split_witness_file(&old_w).expect("corpus witness.bin");
    let bytes_equal = old_sw == wb && old_c == claim;
    let mut codes: Vec<Vec<u8>> = Vec::new();
    let mut code_meta = Vec::new();
    let mut missing = Vec::new();
    for h in accesses {
        match reg.get(h) {
            Some((n, c)) => {
                codes.push(c.clone());
                code_meta.push(json!({"hash": h.to_string(), "name": n, "len": c.len()}));
            }
            None => missing.push(h.to_string()),
        }
    }
    let cold_nc = judge.judge(ci, client, wb, &[], rs, None);
    let cold = judge.judge(ci, client, wb, &codes, rs, None);
    let mut meta: serde_json::Value = serde_json::from_slice(&std::fs::read(src.join("meta.json")).unwrap()).unwrap();
    meta["nearcore"] = json!(vstr(&cold));
    meta["expected_rel"] = json!(cold.is_ok());
    for d in ["d0", "d1", "d2"] {
        let inn = meta[format!("in_{d}")].as_bool().unwrap_or(false);
        meta[format!("expected_rel_{d}")] = json!(cold.is_ok() && inn);
    }
    meta["verdict_source"] = json!("nearcore(cold)");
    meta["nearcore_judge"] = json!("cold validator (empty compiled-contract cache) with the appended code blobs");
    meta["nearcore_warm_no_codes"] = json!(vstr(warm));
    meta["nearcore_cold_no_codes"] = json!(vstr(&cold_nc));
    meta["contract_accesses"] = json!(accesses.iter().map(|h| h.to_string()).collect::<Vec<_>>());
    meta["codes"] = json!(code_meta);
    meta["regenerated_from"] = json!(format!("d2corpus.v2/{sub}/{name}"));
    if bytes_equal && missing.is_empty() {
        let d = out.join(sub).join(name);
        std::fs::create_dir_all(&d).unwrap();
        std::fs::write(d.join("claim.bin"), claim).unwrap();
        std::fs::write(d.join("witness.bin"), crate::enc::encode_witness(wb, &codes)).unwrap();
        std::fs::write(d.join("meta.json"), serde_json::to_string_pretty(&meta).unwrap()).unwrap();
    }
    json!({
        "case": format!("{sub}/{name}"), "bytes_equal": bytes_equal, "corpus_codes": old_codes,
        "accesses": accesses.len(), "codes_missing_from_registry": missing,
        "warm_no_codes": vstr(warm), "cold_no_codes": vstr(&cold_nc), "cold_with_codes": vstr(&cold),
        "corpus_nearcore": meta.get("regenerated_from").cloned(),
    })
}

/// `chaind2::craft_for_d2` (private there), unchanged.
fn craft_for_d2(s: &Setup, k: usize, block: &near_chain::Block, height: u64, p: &ChainParams, rng: &mut StdRng) -> Option<Vec<(String, SignedTransaction)>> {
    let c0 = &s.env.clients[0];
    let layout = c0.epoch_manager.get_shard_layout(block.header().epoch_id()).unwrap();
    let sid = layout.account_id_to_shard_id(&s.accounts[k][0]);
    let uid = near_primitives::shard_layout::ShardUId::from_shard_id_and_layout(sid, &layout);
    let (c, extra) = s.env.clients.iter().find_map(|c| c.chain.get_chunk_extra(block.hash(), &uid).ok().map(|e| (c, e)))?;
    let trie = c.runtime_adapter.get_trie_for_shard(sid, block.hash(), *extra.state_root(), false).unwrap();
    let mut view = HashMap::new();
    for j in 5..ACCTS_PER_SHARD {
        let a = &s.accounts[k][j];
        let acc = near_store::get_account(&trie, a).unwrap().unwrap();
        let ak = near_store::get_access_key(&trie, a, &InMemorySigner::test_signer(a).public_key()).unwrap().map(|x| x.nonce).unwrap_or(0);
        let gk = if j == 6 {
            let pk = crate::d1gen::gk_signer(a).public_key();
            near_store::get_access_key(&trie, a, &pk).unwrap().and_then(|k| k.gas_key_info().map(|g| g.balance.as_yoctonear())).map(|bal| {
                let ns = (0..2u16).map(|i| near_store::get_gas_key_nonce(&trie, a, &pk, i).unwrap().unwrap_or(0)).collect();
                (bal, ns)
            })
        } else {
            None
        };
        view.insert(a.clone(), crate::d2gen::Reserved { amount: acc.amount().as_yoctonear(), ak_nonce: ak, gk, fc_nonce: 0 });
    }
    let cfg = RuntimeConfigStore::new(None).get_config(86).clone();
    let mut ctx = crate::d2gen::CraftCtx {
        accounts: &s.accounts,
        k,
        n_shards: p.n_shards,
        apply_height: height + 1,
        gas_price: block.header().next_gas_price().as_yoctonear(),
        tip_hash: *block.hash(),
        config: &cfg,
        view,
    };
    let n = rng.gen_range(2..7);
    Some(crate::d2gen::craft(rng, &mut ctx, n, 0.1))
}

