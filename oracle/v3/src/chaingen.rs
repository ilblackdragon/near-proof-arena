//! Chain generation with nearcore's own TestEnv (real NightshadeRuntime, epoch
//! manager, block and chunk production, real witness production), witness
//! capture, claim building, nearcore judging, D0 classification, mutants.

use crate::claim::{block_rec, build_claim};
use crate::enc::{Claim, encode_witness};
use crate::judge::nearcore_judge;
use crate::mutate::{Judge, drop_each_node, mutants};
use integration_tests::env::nightshade_setup::TestEnvNightshadeSetupExt;
use integration_tests::env::test_env::TestEnv;
use near_chain::Provenance;
use near_chain::chain::ChunkStateWitnessMessage;
use near_chain::stateless_validation::processing_tracker::ProcessingDoneTracker;
use near_chain_configs::{Genesis, GenesisConfig, GenesisRecords};
use near_crypto::InMemorySigner;
use near_epoch_manager::{EpochManager, EpochManagerAdapter, EpochManagerHandle};
use near_parameters::RuntimeConfigStore;
use near_primitives::account::{AccessKey, AccountContract};
use near_primitives::action::{Action, TransferAction};
use near_primitives::epoch_manager::{EpochConfig, EpochConfigStore};
use near_primitives::num_rational::Rational32;
use near_primitives::shard_layout::ShardLayout;
use near_primitives::state_record::StateRecord;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::test_utils::create_test_signer;
use near_primitives::transaction::SignedTransaction;
use near_primitives::types::{AccountId, AccountInfo, Balance, Gas, NumSeats};
use near_primitives::version::PROTOCOL_VERSION;
use near_primitives_core::account::Account;
use near_store::test_utils::create_test_store;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde_json::json;
use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct ChainParams {
    pub seed: u64,
    pub n_shards: usize,
    pub seats: NumSeats,
    pub gas_limit_tgas: u64,
    pub epoch_length: u64,
    pub blocks: u64,
    pub p_missing: f64,
    pub p_tx_shard: f64,
    pub p_burst: f64,
    pub p_fail: f64,
    pub p_implicit: f64,
    pub p_two: f64,
    /// (first round, number of rounds, shard index): force that shard's chunks missing for a
    /// long run (segments longer than 32 blocks: D0 exclusion c.segment).
    pub long_skip: Option<(u64, u64, usize)>,
    /// Domain-D1 mode (src/d1gen.rs): extra genesis keys, honest traffic on accounts
    /// a00..a04 (incl. self-transfers and V1 transactions), crafted transactions of every
    /// validity class injected by an adversarial chunk producer with probability `p_adv`
    /// per height, classification against D1.
    pub d1: bool,
    pub p_adv: f64,
}

const ACCTS_PER_SHARD: usize = 10;
const N_VALIDATORS: usize = 8;

fn acct(k: usize, j: usize) -> AccountId {
    format!("s{k}a{j:02}").parse().unwrap()
}

pub struct Setup {
    pub clock: near_time::FakeClock,
    pub env: TestEnv,
    pub ems: Vec<Arc<EpochManagerHandle>>,
    pub genesis: Genesis,
    pub accounts: Vec<Vec<AccountId>>,
}

pub fn setup(p: &ChainParams) -> Setup {
    let accounts: Vec<Vec<AccountId>> =
        (0..p.n_shards).map(|k| (0..ACCTS_PER_SHARD).map(|j| acct(k, j)).collect()).collect();
    let boundaries: Vec<AccountId> = (1..p.n_shards).map(|k| format!("s{k}").parse().unwrap()).collect();
    let shard_layout = ShardLayout::multi_shard_custom(boundaries, 3);
    let validators: Vec<AccountId> =
        (0..N_VALIDATORS).map(|i| acct(i % p.n_shards, i / p.n_shards)).collect();
    let initial_balance = Balance::from_near(1_000_000);
    let validator_stake = Balance::from_near(1_000_000);
    let mut genesis_config = GenesisConfig {
        protocol_version: PROTOCOL_VERSION,
        genesis_height: 10000,
        genesis_time: chrono::DateTime::from_timestamp(1_700_000_000, 0).unwrap(),
        chain_id: "arena-v3-local".to_string(),
        shard_layout,
        validators: validators
            .iter()
            .map(|a| AccountInfo {
                account_id: a.clone(),
                public_key: create_test_signer(a.as_str()).public_key(),
                amount: validator_stake,
            })
            .collect(),
        epoch_length: p.epoch_length,
        transaction_validity_period: 50,
        protocol_treasury_account: accounts[p.n_shards - 1][ACCTS_PER_SHARD - 1].clone(),
        num_block_producer_seats: p.seats,
        minimum_validators_per_shard: 1,
        gas_limit: Gas::from_teragas(p.gas_limit_tgas),
        block_producer_kickout_threshold: 0,
        chunk_producer_kickout_threshold: 0,
        chunk_validator_only_kickout_threshold: 0,
        online_min_threshold: Rational32::new(0, 1),
        online_max_threshold: Rational32::new(1, 1000),
        protocol_reward_rate: Rational32::new(1, 10),
        max_inflation_rate: Rational32::new(1, 1),
        ..Default::default()
    };
    let mut records = Vec::new();
    for a in accounts.iter().flatten() {
        let staked = if validators.contains(a) { validator_stake } else { Balance::ZERO };
        records.push(StateRecord::Account {
            account_id: a.clone(),
            account: Account::new(initial_balance, staked, AccountContract::None, 0),
        });
        records.push(StateRecord::access_key(
            a.clone(),
            &create_test_signer(a.as_str()).public_key(),
            AccessKey::full_access(),
        ));
        genesis_config.total_supply = genesis_config
            .total_supply
            .checked_add(initial_balance)
            .unwrap()
            .checked_add(staked)
            .unwrap();
    }
    if p.d1 {
        records.extend(crate::d1gen::genesis_records(&accounts));
    }
    let genesis = Genesis::new(genesis_config, GenesisRecords(records)).unwrap();
    let n = validators.len();
    let stores: Vec<_> = (0..n).map(|_| create_test_store()).collect();
    let mut base: EpochConfig = (&genesis.config).into();
    base.block_producer_kickout_threshold = 0;
    base.chunk_producer_kickout_threshold = 0;
    let ecs = EpochConfigStore::test(BTreeMap::from_iter(vec![(
        genesis.config.protocol_version,
        Arc::new(base),
    )]));
    let ems: Vec<Arc<EpochManagerHandle>> = stores
        .iter()
        .map(|s| EpochManager::new_arc_handle_from_epoch_config_store(s.clone(), &genesis.config, ecs.clone()))
        .collect();
    // Deterministic time: a fake clock advanced by a fixed step per block, so the
    // generated chain (timestamps, hence every hash) is byte-reproducible from the seed.
    let clock = near_time::FakeClock::new(near_time::Utc::from_unix_timestamp(1_700_000_000).unwrap());
    let env = TestEnv::builder(&genesis.config)
        .clock(clock.clock())
        .clients(validators.clone())
        .stores(stores)
        .epoch_managers(ems.clone())
        .save_tx_outcomes(true)
        .nightshade_runtimes_with_runtime_config_store(&genesis, vec![RuntimeConfigStore::new(None); n])
        .build();
    Setup { clock, env, ems, genesis, accounts }
}

pub struct Stats {
    pub d1: usize,
    pub injected: usize,
    pub honest: usize,
    pub honest_ok: usize,
    pub d0: usize,
    pub ood_written: usize,
    pub mutants: usize,
    pub by_violation: BTreeMap<String, usize>,
}

fn write_case(dir: &Path, claim: &Claim, witness: &[u8], meta: serde_json::Value) {
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("claim.bin"), claim.encode()).unwrap();
    std::fs::write(dir.join("witness.bin"), encode_witness(witness, &[])).unwrap();
    std::fs::write(dir.join("meta.json"), serde_json::to_string_pretty(&meta).unwrap()).unwrap();
}

/// Run one chain; write cases under `out/<chain>-...`.
pub fn run_chain(
    chain_idx: usize,
    p: &ChainParams,
    out: &Path,
    ood_cap: usize,
    mutate_every: usize,
    stats: &mut Stats,
) {
    let mut s = setup(p);
    let mut rng = StdRng::seed_from_u64(p.seed);
    let mut nonces: HashMap<AccountId, u64> = HashMap::new();
    let mut fail_ctr = 0u64;
    let mut ood_count: BTreeMap<String, usize> = BTreeMap::new();
    let mut d0_seen = 0usize;
    let mut pending_skips: HashMap<u64, Vec<AccountId>> = HashMap::new();
    let mut labels: HashMap<near_primitives::hash::CryptoHash, String> = HashMap::new();
    let tip0 = s.env.clients[0].chain.head().unwrap();
    let mut height = tip0.height;
    let rs = (
        s.env.clients[0].epoch_manager.num_data_parts() as u16,
        s.env.clients[0].epoch_manager.num_total_parts() as u16,
    );
    for _round in 0..p.blocks {
        height += 1;
        s.clock.advance(near_time::Duration::milliseconds(1100));
        let tip = s.env.clients[0].chain.head().unwrap();
        // ---- transactions
        let mut txs = Vec::new();

        for k in 0..p.n_shards {
            if !rng.gen_bool(p.p_tx_shard) {
                continue;
            }
            let burst = rng.gen_bool(p.p_burst);
            let n = if burst { rng.gen_range(400..900) } else { rng.gen_range(1..5) };
            let tgt_shard = (k + rng.gen_range(1..p.n_shards)) % p.n_shards;
            if burst && rng.gen_bool(0.7) {
                // Make the target shard's chunk at height+1 missing, so the link to it is
                // disallowed when the burst's receipts are produced: they get buffered and
                // the sender shard emits bandwidth requests (scheduler requests path).
                let layout = s.env.clients[0].epoch_manager.get_shard_layout(
                    &s.env.clients[0].epoch_manager.get_epoch_id_from_prev_block(&tip.last_block_hash).unwrap(),
                ).unwrap();
                let tgt_id = layout.shard_ids().nth(tgt_shard).unwrap();
                let tgt_acct = &s.accounts[tgt_shard][0];
                let sid = layout.account_id_to_shard_id(tgt_acct);
                let _ = tgt_id;
                for off in 2..=4u64 {
                    let a = s.env.get_chunk_producer_at_offset(&tip, off, sid);
                    pending_skips.entry(tip.height + off).or_default().push(a);
                }
            }
            let n_acc = if p.d1 { crate::d1gen::HONEST_ACCTS } else { ACCTS_PER_SHARD };
            for _ in 0..n {
                let signer_id = s.accounts[k][rng.gen_range(0..n_acc)].clone();
                let signer = InMemorySigner::test_signer(&signer_id);
                let nonce = nonces.entry(signer_id.clone()).or_insert(0);
                *nonce += 1;
                let ts = if burst { tgt_shard } else { rng.gen_range(0..p.n_shards) };
                let (receiver, actions) = if rng.gen_bool(p.p_fail) {
                    fail_ctr += 1;
                    (format!("s{ts}zz{fail_ctr}").parse().unwrap(), 1)
                } else if rng.gen_bool(p.p_implicit) {
                    let h: [u8; 32] = rng.r#gen();
                    (hex::encode(h).parse().unwrap(), 1)
                } else if rng.gen_bool(p.p_two) {
                    (s.accounts[ts][rng.gen_range(0..n_acc)].clone(), 2)
                } else if p.d1 && rng.gen_bool(0.1) {
                    (signer_id.clone(), 1) // self-transfer: a local receipt
                } else {
                    (s.accounts[ts][rng.gen_range(0..n_acc)].clone(), 1)
                };
                let deposit = Balance::from_yoctonear(rng.gen_range(1..10u128.pow(24)));
                let acts = (0..actions).map(|_| Action::Transfer(TransferAction { deposit })).collect();
                if p.d1 && rng.gen_bool(0.1) {
                    txs.push(SignedTransaction::from_actions_v1(
                        near_primitives::transaction::TransactionNonce::from_nonce(*nonce),
                        signer_id,
                        receiver,
                        &signer,
                        acts,
                        tip.last_block_hash,
                    ));
                } else {
                    txs.push(SignedTransaction::from_actions(
                        *nonce,
                        signer_id,
                        receiver,
                        &signer,
                        acts,
                        tip.last_block_hash,
                    ));
                }
            }
        }
        for tx in txs {
            for h in &s.env.rpc_handlers {
                let _ = h.process_tx(tx.clone(), false, false);
            }
        }
        let mut force_skip: Vec<AccountId> = pending_skips.remove(&(tip.height + 2)).unwrap_or_default();
        if let Some((start, len, k)) = p.long_skip {
            if _round >= start && _round < start + len {
                let em = &s.env.clients[0].epoch_manager;
                let layout = em.get_shard_layout(&em.get_epoch_id_from_prev_block(&tip.last_block_hash).unwrap()).unwrap();
                let sid = layout.account_id_to_shard_id(&s.accounts[k][0]);
                force_skip.push(s.env.get_chunk_producer_at_offset(&tip, 2, sid));
            }
        }
        // ---- adversarial chunk producer (D1): the producer of shard `k` at height+1
        let inject: Option<(usize, AccountId)> = if p.d1 && rng.gen_bool(p.p_adv) {
            let k = rng.gen_range(0..p.n_shards);
            let em = &s.env.clients[0].epoch_manager;
            let layout = em.get_shard_layout(&em.get_epoch_id_from_prev_block(&tip.last_block_hash).unwrap()).unwrap();
            let sid = layout.account_id_to_shard_id(&s.accounts[k][0]);
            Some((k, s.env.get_chunk_producer_at_offset(&tip, 2, sid)))
        } else {
            None
        };
        // ---- block
        let bp = s.env.get_block_producer_at_offset(&tip, height - tip.height);
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
                // the block may not be applied yet (ChunksMissing): then no crafted chunk
                let Some(crafted) = craft_for(&s, i, k, &block, height, _round, p, &mut rng) else {
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
            let r = r.map(|_| ());
            match r {
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
        for (ci, c) in s.env.clients.iter().enumerate() {
            if c.chain.head().unwrap().last_block_hash != *block.hash() { eprintln!("h{height}: client {ci} stuck"); }
        }
        for c in &s.env.clients {
            assert_eq!(c.chain.head().unwrap().last_block_hash, *block.hash(), "client did not finish block");
        }
        // ---- capture + deliver witnesses (as TestEnv::propagate_chunk_state_witnesses)
        let mut captured: Vec<(usize, ChunkStateWitness)> = Vec::new();
        let mut waiters = Vec::new();
        let adapters = s.env.partial_witness_adapters.clone();
        for (ci, ad) in adapters.iter().enumerate() {
            while let Some(req) = ad.pop_distribution_request() {
                let sw = req.state_witness;
                captured.push((ci, sw.clone()));
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
                    let _ = s.env.chunk_validation_actors[idx].process_chunk_state_witness_message(
                        ChunkStateWitnessMessage { witness: sw.clone(), raw_witness_size: raw, processing_done_tracker: Some(t) },
                    );
                }
            }
        }
        for wt in waiters {
            wt.wait();
        }
        s.env.propagate_chunk_endorsements(true);

        // ---- judge, classify, write
        for (ci, sw) in captured {
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
            let verdict = nearcore_judge(client, &wb, &[], (built.claim.rs_data_parts, built.claim.rs_total_parts));
            if verdict.is_ok() {
                stats.honest_ok += 1;
            } else {
                eprintln!("honest witness rejected by nearcore: {:?}", verdict);
            }
            // classify on a client that tracks the main transition's shard (has its ChunkExtra/state)
            let tracker = (0..s.env.clients.len())
                .map(|k| &s.env.clients[k])
                .find(|c| crate::d0::tracks(c, &built))
                .unwrap_or(client);
            let viol = match crate::d0::classify(tracker, &built, &sw, wb.len(), 0) {
                Ok(v) => v,
                Err(e) => {
                    eprintln!("classify failed: {e}");
                    continue;
                }
            };
            let in_d0 = viol.is_empty();
            let (viol1, in_d1) = if p.d1 {
                match crate::d1::classify(tracker, &built, &sw, &viol) {
                    Ok(v1) => {
                        let e = v1.is_empty();
                        (v1, e)
                    }
                    Err(e) => {
                        eprintln!("d1 classify failed: {e}");
                        continue;
                    }
                }
            } else {
                (viol.clone(), in_d0)
            };
            if in_d0 && !in_d1 {
                panic!("D0 case outside D1: {viol1:?}");
            }
            let tx_results = crate::d1::tx_results(tracker, &built, &sw);
            let tx_labels: Vec<String> = sw
                .transactions()
                .iter()
                .map(|t| labels.get(&t.get_hash()).cloned().unwrap_or_else(|| "honest".into()))
                .collect();
            let new_tx_labels: Vec<String> = sw
                .new_transactions()
                .iter()
                .map(|t| labels.get(&t.get_hash()).cloned().unwrap_or_else(|| "honest".into()))
                .collect();
            let key = sw.chunk_production_key();
            let name = format!("{chain_idx:02}-h{}-s{}", key.height_created, key.shard_id);
            for v in if p.d1 { &viol1 } else { &viol } {
                *stats.by_violation.entry(v.to_string()).or_default() += 1;
            }
            let features = json!({
                "n_shards": p.n_shards,
                "rs": [built.claim.rs_data_parts, built.claim.rs_total_parts],
                "n_blocks": built.claim.blocks.len(),
                "n_implicit": built.implicit.len(),
                "n_source_blocks": built.source.len(),
                "n_source_proofs": match &sw { ChunkStateWitness::V2(x) => x.source_receipt_proofs.len() },
                "n_receipts": match &sw { ChunkStateWitness::V2(x) => x.source_receipt_proofs.values().map(|p| p.0.len()).sum::<usize>() },
                "bw_requests_in_context": built.blocks.iter().any(|b| b.chunks().iter_raw().any(|c| c.bandwidth_requests().map_or(false, |r| match r { near_primitives::bandwidth_scheduler::BandwidthRequests::V1(v) => !v.requests.is_empty() }))),
                "other_congestion_nonzero": built.blocks.iter().any(|b| b.chunks().iter_raw().any(|c| { let ci = c.congestion_info(); ci.delayed_receipts_gas() != 0 || ci.buffered_receipts_gas() != 0 || ci.receipt_bytes() != 0 })),
                "witness_bytes": wb.len(),
            });
            let meta = json!({
                "case": name, "kind": "honest", "chain_params": format!("{p:?}"),
                "nearcore": verdict.as_ref().map(|_| "ok".to_string()).unwrap_or_else(|e| e.clone()),
                "expected_rel": verdict.is_ok(),
                "in_d0": in_d0, "d0_violations": viol,
                "expected_rel_d0": verdict.is_ok() && in_d0,
                "in_d1": in_d1, "d1_violations": viol1,
                "expected_rel_d1": verdict.is_ok() && in_d1,
                "tx_labels": tx_labels, "tx_results": tx_results, "new_tx_labels": new_tx_labels,
                "features": features,
            });
            let in_dom = if p.d1 { in_d1 } else { in_d0 };
            if in_dom {
                if in_d0 {
                    stats.d0 += 1;
                }
                if in_d1 {
                    stats.d1 += 1;
                }
                write_case(&out.join(if p.d1 { "d1" } else { "d0" }).join(&name), &built.claim, &wb, meta);
                d0_seen += 1;
                if verdict.is_ok() && mutate_every > 0 && d0_seen % mutate_every == 0 {
                    let last = built.blocks.last().unwrap();
                    let parent = if last.header().is_genesis() {
                        None
                    } else {
                        client.chain.get_block(last.header().prev_hash()).ok().and_then(|b| block_rec(&b).ok())
                    };
                    let mut ms: Vec<(crate::mutate::Mutant, Option<Vec<u8>>)> =
                        mutants(&built.claim, &sw, parent, &mut rng).into_iter().map(|m| (m, None)).collect();
                    if d0_seen % (mutate_every * 2) == 0 {
                        ms.extend(drop_each_node(&built.claim, &sw, if p.d1 { 64 } else { 48 }).into_iter().map(|m| (m, None)));
                    }
                    if p.d1 {
                        ms.extend(crate::d1::mutants(client, &built.claim, &sw, &mut rng));
                    }
                    for (m, flags) in ms {
                        let (exp, src) = match (&m.judge, &flags) {
                            (Judge::Claim, _) => (Err("claim-v3 discipline".to_string()), "claim-v3"),
                            (Judge::Nearcore, None) => (
                                nearcore_judge(client, &m.witness, &[], (m.claim.rs_data_parts, m.claim.rs_total_parts)),
                                "nearcore",
                            ),
                            (Judge::Nearcore, Some(f)) => (
                                crate::judge::nearcore_judge_flags(client, &m.witness, (m.claim.rs_data_parts, m.claim.rs_total_parts), f),
                                "nearcore(tx_valid=claim)",
                            ),
                        };
                        let mname = format!("{name}-{}", m.name);
                        // dropping the only new transaction of a base whose sole D0 violation is
                        // w.no_txs (and that has no `transactions`) yields a D0 case
                        let in_d0 = in_d0
                            || (m.name == "w.new_tx.drop_rehashed"
                                && viol == ["w.no_txs"]
                                && sw.transactions().is_empty()
                                && sw.new_transactions().len() == 1);
                        let meta = json!({
                            "case": mname, "kind": "mutant", "mutation": m.name, "base": name,
                            "verdict_source": src,
                            "nearcore": exp.as_ref().map(|_| "ok".to_string()).unwrap_or_else(|e| e.clone()),
                            "expected_rel": exp.is_ok(),
                            "in_d0": in_d0, "d0_violations": viol,
                            "expected_rel_d0": exp.is_ok() && in_d0,
                            "in_d1": in_d1,
                            "expected_rel_d1": exp.is_ok() && in_d1,
                        });
                        stats.mutants += 1;
                        write_case(&out.join("mutants").join(&mname), &m.claim, &m.witness, meta);
                    }
                }
            } else {
                let fam = viol.join("+");
                let c = ood_count.entry(fam).or_default();
                if *c < ood_cap {
                    *c += 1;
                    stats.ood_written += 1;
                    write_case(&out.join("ood").join(&name), &built.claim, &wb, meta);
                }
            }
        }
    }
    let _ = rs;
}

/// Crafted transactions for shard index `k`, from the exact state after `block` (the state the
/// crafted chunk's transactions are applied to).
#[allow(clippy::too_many_arguments)]
fn craft_for(
    s: &Setup,
    _i: usize,
    k: usize,
    block: &near_chain::Block,
    height: u64,
    round: u64,
    p: &ChainParams,
    rng: &mut StdRng,
) -> Option<Vec<(String, SignedTransaction)>> {
    let c0 = &s.env.clients[0];
    let layout = c0.epoch_manager.get_shard_layout(block.header().epoch_id()).unwrap();
    let sid = layout.account_id_to_shard_id(&s.accounts[k][0]);
    let uid = near_primitives::shard_layout::ShardUId::from_shard_id_and_layout(sid, &layout);
    let (c, extra) = s
        .env
        .clients
        .iter()
        .find_map(|c| c.chain.get_chunk_extra(block.hash(), &uid).ok().map(|e| (c, e)))?;
    let trie = c.runtime_adapter.get_trie_for_shard(sid, block.hash(), *extra.state_root(), false).unwrap();
    let mut view = HashMap::new();
    for j in crate::d1gen::HONEST_ACCTS..ACCTS_PER_SHARD {
        let a = &s.accounts[k][j];
        let acc = near_store::get_account(&trie, a).unwrap().unwrap();
        let ak = near_store::get_access_key(&trie, a, &InMemorySigner::test_signer(a).public_key())
            .unwrap()
            .map(|x| x.nonce)
            .unwrap_or(0);
        view.insert(
            a.clone(),
            crate::d1gen::AcctView { amount: acc.amount().as_yoctonear(), storage_usage: acc.storage_usage(), ak_nonce: ak },
        );
    }
    let cfg = RuntimeConfigStore::new(None).get_config(86).clone();
    let old_hash = if round > 60 { *c.chain.genesis_block().hash() } else { near_primitives::hash::CryptoHash(rng.r#gen()) };
    let mut ctx = crate::d1gen::Ctx {
        accounts: &s.accounts,
        k,
        n_shards: p.n_shards,
        apply_height: height + 1,
        gas_price: block.header().next_gas_price().as_yoctonear(),
        tip_hash: *block.hash(),
        old_hash,
        config: &cfg,
        view,
    };
    let n = rng.gen_range(3..10);
    Some(crate::d1gen::craft(rng, &mut ctx, n, 0.08))
}
