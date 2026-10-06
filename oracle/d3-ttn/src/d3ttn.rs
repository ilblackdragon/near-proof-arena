//! d3-ttn: does trie-node gas accounting (TTN: `touching_trie_node`,
//! `read_cached_trie_node`) depend on how a node applies a chunk?
//!
//! A real multi-shard TestEnv (mainnet runtime config, PV86) runs a storage-heavy
//! contract (`ttn.wasm`, from `ttn.wat`). For every chunk whose witness a chunk producer
//! emits, the SAME chunk is compared across:
//!   P  the producer's own application (outcomes stored by the chain while it
//!      processed the block: `StorageDataSource::Db`, flat storage, and
//!      memtries iff `--memtries`), read back from its chain store;
//!   V  the stateless validator's application of the witness: nearcore's
//!      `pre_validate_chunk_state_witness` + `update_shard::apply_new_chunk`
//!      with `ApplyChunkReason::ValidateChunkStateWitness` (exactly what
//!      `validate_chunk_state_witness_impl` runs; `StorageDataSource::Recorded`,
//!      `use_flat_storage: true` hard-coded in apply_new_chunk);
//!   A  ablation: the same recorded storage applied with `use_flat_storage:
//!      false` (`Trie::from_recorded_storage(.., false)` → `use_access_tracker
//!      = true`, i.e. reads also counted). Expected to DIFFER whenever a read
//!      or has_key touched the trie — this shows the comparison is sensitive.
//! plus nearcore's full witness judge (endorsement) on every witness.
//! Per outcome we compare the borsh bytes of `ExecutionOutcome` (gas_burnt,
//! tokens_burnt, status, logs, receipt ids, metadata incl. the full gas
//! profile) and the per-chunk ChunkExtra gas; `compute_usage` is not stored
//! (`#[borsh(skip)]`), it is a function of the profile (cp3 compute model).
//! A JSON digest per chunk is written so runs with/without memtries can be
//! diffed (same seed ⇒ same chain).

use crate::judge::{nearcore_judge, pre_validate};
use integration_tests::env::test_env::TestEnv;
use near_chain::Provenance;
use near_chain::chain::ChunkStateWitnessMessage;
use near_chain::stateless_validation::chunk_validation::MainTransition;
use near_chain::stateless_validation::processing_tracker::ProcessingDoneTracker;
use near_chain::types::{
    ApplyChunkShardContext, MaybePinnedMemtrieRoot, RuntimeStorageConfig, StorageDataSource,
};
use near_chain::update_shard::{NewChunkData, ShardContext, apply_new_chunk};
use near_chain::ChainStoreAccess;
use near_chain_configs::{DEFAULT_GC_NUM_EPOCHS_TO_KEEP, Genesis, GenesisConfig, GenesisRecords};
use near_crypto::InMemorySigner;
use near_epoch_manager::shard_assignment::shard_id_to_uid;
use near_epoch_manager::{EpochManager, EpochManagerAdapter, EpochManagerHandle};
use near_parameters::{ExtCosts, RuntimeConfigStore};
use near_primitives::account::{AccessKey, AccountContract};
use near_primitives::apply::ApplyChunkReason;
use near_primitives::epoch_manager::{EpochConfig, EpochConfigStore};
use near_primitives::hash::{CryptoHash, hash};
use near_primitives::num_rational::Rational32;
use near_primitives::shard_layout::ShardLayout;
use near_primitives::state_record::StateRecord;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::test_utils::create_test_signer;
use near_primitives::transaction::{ExecutionMetadata, ExecutionOutcomeWithId, SignedTransaction};
use near_primitives::types::validator_stake::ValidatorStakeIter;
use near_primitives::types::{AccountId, AccountInfo, Balance, Gas};
use near_primitives::version::PROTOCOL_VERSION;
use near_primitives_core::account::Account;
use near_store::TrieConfig;
use near_store::genesis::initialize_genesis_state;
use near_store::test_utils::create_test_store;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde_json::json;
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

const CONTRACT: &[u8] = include_bytes!("../ttn.wasm");
const ACCTS: usize = 6;
const N_VALIDATORS: usize = 8;

fn acct(k: usize, j: usize) -> AccountId {
    format!("s{k}a{j:02}").parse().unwrap()
}
fn ctr(k: usize) -> AccountId {
    format!("s{k}ctr").parse().unwrap()
}

pub struct Params {
    pub seed: u64,
    pub n_shards: usize,
    pub blocks: u64,
    pub memtries: bool,
    pub ops_max: usize,
    /// op-level difftest trace (`--trace FILE`): per chunk, the recorded pre-state, the
    /// contract calls in execution order, and nearcore's per-call profile
    pub trace: Option<std::path::PathBuf>,
}

fn setup(p: &Params) -> (near_time::FakeClock, TestEnv, Vec<Vec<AccountId>>) {
    let accounts: Vec<Vec<AccountId>> =
        (0..p.n_shards).map(|k| (0..ACCTS).map(|j| acct(k, j)).collect()).collect();
    let boundaries: Vec<AccountId> = (1..p.n_shards).map(|k| format!("s{k}").parse().unwrap()).collect();
    let validators: Vec<AccountId> = (0..N_VALIDATORS).map(|i| acct(i % p.n_shards, i / p.n_shards)).collect();
    let initial = Balance::from_near(1_000_000);
    let stake = Balance::from_near(1_000_000);
    let mut gc = GenesisConfig {
        protocol_version: PROTOCOL_VERSION,
        genesis_height: 10000,
        genesis_time: chrono::DateTime::from_timestamp(1_700_000_000, 0).unwrap(),
        chain_id: "arena-v3-ttn".to_string(),
        shard_layout: ShardLayout::multi_shard_custom(boundaries, 3),
        validators: validators
            .iter()
            .map(|a| AccountInfo {
                account_id: a.clone(),
                public_key: create_test_signer(a.as_str()).public_key(),
                amount: stake,
            })
            .collect(),
        epoch_length: 30,
        transaction_validity_period: 50,
        protocol_treasury_account: accounts[p.n_shards - 1][ACCTS - 1].clone(),
        num_block_producer_seats: N_VALIDATORS as u64,
        minimum_validators_per_shard: 1,
        gas_limit: Gas::from_teragas(1000),
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
    let code_hash = hash(CONTRACT);
    let mut add = |records: &mut Vec<StateRecord>, a: &AccountId, staked: Balance, contract: bool| {
        let ac = if contract { AccountContract::Local(code_hash) } else { AccountContract::None };
        records.push(StateRecord::Account { account_id: a.clone(), account: Account::new(initial, staked, ac, 0) });
        records.push(StateRecord::access_key(
            a.clone(),
            &create_test_signer(a.as_str()).public_key(),
            AccessKey::full_access(),
        ));
        gc.total_supply = gc.total_supply.checked_add(initial).unwrap().checked_add(staked).unwrap();
    };
    for a in accounts.iter().flatten() {
        let staked = if validators.contains(a) { stake } else { Balance::ZERO };
        add(&mut records, a, staked, false);
    }
    for k in 0..p.n_shards {
        let c = ctr(k);
        add(&mut records, &c, Balance::ZERO, true);
        records.push(StateRecord::Contract { account_id: c.clone(), code: CONTRACT.to_vec() });
        // pre-populate half of the 2-byte keys and some 3-byte keys, mixed value sizes
        for j in (0..64u8).step_by(2) {
            let vlen = [1usize, 100, 4500][(j as usize / 2) % 3];
            records.push(StateRecord::Data {
                account_id: c.clone(),
                data_key: vec![b'k', j].into(),
                value: vec![j; vlen].into(),
            });
            if j % 6 == 0 {
                records.push(StateRecord::Data {
                    account_id: c.clone(),
                    data_key: vec![b'k', j, 0x55].into(),
                    value: vec![j; 100].into(),
                });
            }
        }
    }
    let genesis = Genesis::new(gc, GenesisRecords(records)).unwrap();
    let n = validators.len();
    let stores: Vec<_> = (0..n).map(|_| create_test_store()).collect();
    let mut base: EpochConfig = (&genesis.config).into();
    base.block_producer_kickout_threshold = 0;
    base.chunk_producer_kickout_threshold = 0;
    let ecs = EpochConfigStore::test(BTreeMap::from_iter(vec![(genesis.config.protocol_version, Arc::new(base))]));
    let ems: Vec<Arc<EpochManagerHandle>> = stores
        .iter()
        .map(|s| EpochManager::new_arc_handle_from_epoch_config_store(s.clone(), &genesis.config, ecs.clone()))
        .collect();
    let clock = near_time::FakeClock::new(near_time::Utc::from_unix_timestamp(1_700_000_000).unwrap());
    let trie_config = TrieConfig { load_memtries_for_tracked_shards: p.memtries, ..TrieConfig::default() };
    let g2 = genesis.clone();
    let env = TestEnv::builder(&genesis.config)
        .clock(clock.clock())
        .clients(validators.clone())
        .stores(stores)
        .epoch_managers(ems)
        .save_tx_outcomes(true)
        .internal_initialize_nightshade_runtimes(
            vec![RuntimeConfigStore::new(None); n],
            vec![trie_config; n],
            move |home_dir, store, cache, em, rcs, tc| {
                initialize_genesis_state(store.clone(), &g2, Some(home_dir.as_path()));
                near_chain::runtime::NightshadeRuntime::test_with_trie_config(
                    home_dir.as_path(),
                    store,
                    cache,
                    &g2.config,
                    em,
                    Some(rcs),
                    tc,
                    DEFAULT_GC_NUM_EPOCHS_TO_KEEP,
                    false,
                    1,
                    true,
                )
            },
        )
        .build();
    (clock, env, accounts)
}

fn profile_gas(m: &ExecutionMetadata, c: ExtCosts) -> u64 {
    match m {
        ExecutionMetadata::V3(p) => p.get_ext_cost(c).as_gas(),
        ExecutionMetadata::V4(p) => p.profile.get_ext_cost(c).as_gas(),
        _ => 0,
    }
}

fn outcome_bytes(o: &ExecutionOutcomeWithId) -> Vec<u8> {
    borsh::to_vec(&o.outcome).unwrap()
}

#[derive(Default)]
struct Tally {
    chunks: usize,
    chunks_with_outcomes: usize,
    outcomes: usize,
    fn_outcomes_with_ttn: usize,
    p_vs_v_diff: usize,
    p_missing: usize,
    chunk_gas_diff: usize,
    a_diff_outcomes: usize,
    a_diff_chunks: usize,
    judge_ok: usize,
    judge_fail: usize,
    ttn_gas_v: u128,
    cached_gas_v: u128,
    ttn_gas_a: u128,
    cached_gas_a: u128,
    memtrie_producers: usize,
    compute_v_vs_a_diff: usize,
    ablation_storage_errors: usize,
}

/// Profile slots compared op-level: the ext costs whose compute differs from gas (the spec's
/// `specialCosts`, `Machine.lean`), in the same order.
const SPECIAL: [ExtCosts; 11] = [
    ExtCosts::storage_write_base,
    ExtCosts::storage_read_base,
    ExtCosts::storage_read_key_byte,
    ExtCosts::storage_read_value_byte,
    ExtCosts::storage_large_read_overhead_base,
    ExtCosts::storage_large_read_overhead_byte,
    ExtCosts::storage_remove_base,
    ExtCosts::storage_has_key_base,
    ExtCosts::storage_has_key_byte,
    ExtCosts::touching_trie_node,
    ExtCosts::read_cached_trie_node,
];

/// One trace line per chunk:
/// `C <prev_root> <n_nodes> <node_hex>… <n_calls> (<account> <prepaid_gas> <args_hex|->
///  <ok|fail> <wasm_gas> <ext_gas_total> <special_0> … <special_10>)…`
/// Calls = the chunk's FunctionCall receipts to the experiment contracts, in execution order
/// (outcome order). Expected values are nearcore's outcome profile (`ProfileDataV3`).
fn write_trace(
    w: &mut impl std::io::Write,
    sw: &ChunkStateWitness,
    root: CryptoHash,
    v: &near_chain::types::ApplyChunkResult,
    calls_by_receipt: &HashMap<CryptoHash, (AccountId, Vec<u8>, u64)>,
) -> bool {
    use near_primitives::state::PartialState;
    use strum::IntoEnumIterator;
    let PartialState::TrieValues(nodes) = &sw.main_state_transition().base_state;
    let mut calls = Vec::new();
    for o in &v.outcomes {
        // contract executions are exactly the outcomes executed by a `s<k>ctr` account
        let ex = o.outcome.executor_id.as_str();
        if !ex.ends_with("ctr") {
            continue;
        }
        let Some((rcv, args, gas)) = calls_by_receipt.get(&o.id) else {
            eprintln!("trace: contract outcome {} with unknown receipt; chunk skipped", o.id);
            return false;
        };
        assert_eq!(rcv.as_str(), ex);
        let prof = match &o.outcome.metadata {
            ExecutionMetadata::V3(p) => p.as_ref().clone(),
            ExecutionMetadata::V4(p) => p.profile.clone(),
            _ => return false,
        };
        let ext: u128 = ExtCosts::iter().map(|c| prof.get_ext_cost(c).as_gas() as u128).sum();
        let status = match o.outcome.status {
            near_primitives::transaction::ExecutionStatus::Failure(_) => "fail",
            _ => "ok",
        };
        let mut c = format!(
            "{} {} {} {} {} {}",
            rcv,
            gas,
            if args.is_empty() { "-".to_string() } else { hex::encode(args) },
            status,
            prof.get_wasm_cost().as_gas(),
            ext
        );
        for k in SPECIAL {
            c.push_str(&format!(" {}", prof.get_ext_cost(k).as_gas()));
        }
        calls.push(c);
    }
    let mut line = format!("C {} {}", hex::encode(root.as_ref()), nodes.len());
    for n in nodes.iter() {
        line.push(' ');
        line.push_str(&hex::encode(n));
    }
    line.push_str(&format!(" {}", calls.len()));
    for c in calls {
        line.push(' ');
        line.push_str(&c);
    }
    writeln!(w, "{line}").unwrap();
    true
}

pub fn cmd_ttn(p: &Params, out: &std::path::Path) {
    let (clock, mut env, accounts) = setup(p);
    // receipt contents: tx hash -> call, then (from the tx's conversion outcome) receipt id -> call
    let mut calls_by_tx: HashMap<CryptoHash, (AccountId, Vec<u8>, u64)> = HashMap::new();
    let mut calls_by_receipt: HashMap<CryptoHash, (AccountId, Vec<u8>, u64)> = HashMap::new();
    let mut trace_skipped = 0usize;
    let mut trace = p.trace.as_ref().map(|f| std::io::BufWriter::new(std::fs::File::create(f).unwrap()));
    let mut rng = StdRng::seed_from_u64(p.seed);
    let mut nonces: HashMap<AccountId, u64> = HashMap::new();
    let mut t = Tally::default();
    let mut digests = Vec::new();
    let mut height = env.clients[0].chain.head().unwrap().height;
    for _round in 0..p.blocks {
        height += 1;
        clock.advance(near_time::Duration::milliseconds(1100));
        let tip = env.clients[0].chain.head().unwrap();
        let mut txs = Vec::new();
        for k in 0..p.n_shards {
            if !rng.gen_bool(0.85) {
                continue;
            }
            for _ in 0..rng.gen_range(1..7) {
                let signer_id = accounts[k][rng.gen_range(0..ACCTS)].clone();
                let signer = InMemorySigner::test_signer(&signer_id);
                let nonce = nonces.entry(signer_id.clone()).or_insert(0);
                *nonce += 1;
                let tgt = ctr(rng.gen_range(0..p.n_shards));
                let nops = rng.gen_range(1..=p.ops_max);
                let mut args = Vec::with_capacity(nops * 3);
                for _ in 0..nops {
                    args.push(rng.gen_range(0..4u8));
                    args.push(rng.gen_range(0..48u8)); // overlap with pre-populated keys 0,2,..,62
                    args.push(rng.gen_range(0..6u8));
                }
                let gas = if rng.gen_bool(0.3) {
                    Gas::from_gas(rng.gen_range(3_000_000_000_000u64..40_000_000_000_000))
                } else {
                    Gas::from_teragas(300)
                };
                let tx = SignedTransaction::call(
                    *nonce,
                    signer_id,
                    tgt.clone(),
                    &signer,
                    Balance::ZERO,
                    "run".to_string(),
                    args.clone(),
                    gas,
                    tip.last_block_hash,
                );
                calls_by_tx.insert(tx.get_hash(), (tgt, args, gas.as_gas()));
                txs.push(tx);
            }
        }
        for tx in txs {
            for h in &env.rpc_handlers {
                let _ = h.process_tx(tx.clone(), false, false);
            }
        }
        let bp = env.get_block_producer_at_offset(&tip, height - tip.height);
        let block = env.client(&bp).produce_block(height).unwrap().unwrap();
        for i in 0..env.clients.len() {
            match env.clients[i].process_block_test(block.clone().into(), Provenance::NONE) {
                Ok(_) | Err(near_chain::Error::ChunksMissing(_)) => {}
                Err(e) => panic!("process_block: {e:?}"),
            }
        }
        for _ in 0..4 {
            env.process_partial_encoded_chunks();
            for j in 0..env.clients.len() {
                env.process_shards_manager_responses_and_finish_processing_blocks(j);
            }
        }
        for c in &env.clients {
            assert_eq!(c.chain.head().unwrap().last_block_hash, *block.hash(), "client did not finish block");
        }
        // capture + deliver witnesses
        let mut captured: Vec<(usize, ChunkStateWitness)> = Vec::new();
        let mut waiters = Vec::new();
        let adapters = env.partial_witness_adapters.clone();
        for (ci, ad) in adapters.iter().enumerate() {
            while let Some(req) = ad.pop_distribution_request() {
                let sw = req.state_witness;
                captured.push((ci, sw.clone()));
                let raw = borsh::object_length(&sw).unwrap();
                let key = sw.chunk_production_key();
                let cvs = env.clients[ci]
                    .epoch_manager
                    .get_chunk_validator_assignments(&key.epoch_id, key.shard_id, key.height_created)
                    .unwrap()
                    .ordered_chunk_validators();
                for a in cvs {
                    if !env.contains_client(&a) {
                        continue;
                    }
                    let idx = env.get_client_index(&a);
                    let tr = ProcessingDoneTracker::new();
                    waiters.push(tr.make_waiter());
                    let _ = env.chunk_validation_actors[idx].process_chunk_state_witness_message(
                        ChunkStateWitnessMessage { witness: sw.clone(), raw_witness_size: raw, processing_done_tracker: Some(tr) },
                    );
                }
            }
        }
        for w in waiters {
            w.wait();
        }
        env.propagate_chunk_endorsements(true);

        for (ci, sw) in captured {
            let client = &env.clients[ci];
            let em: &dyn EpochManagerAdapter = client.epoch_manager.as_ref();
            let rs = (em.num_data_parts() as u16, em.num_total_parts() as u16);
            let wb = borsh::to_vec(&sw).unwrap();
            match nearcore_judge(client, &wb, &[], rs) {
                Ok(()) => t.judge_ok += 1,
                Err(e) => {
                    t.judge_fail += 1;
                    eprintln!("judge rejected honest witness: {e}");
                }
            }
            // V: the validator's main-transition application
            let apply = |flat: bool| -> Option<(CryptoHash, near_primitives::types::ShardId, near_primitives::shard_layout::ShardUId, Result<near_chain::types::ApplyChunkResult, String>, CryptoHash)> {
                let pre = pre_validate(client, &sw).unwrap();
                let MainTransition::NewChunk { new_chunk_data, block_hash, shard_id } = pre.main_transition_params else {
                    return None;
                };
                let epoch_id = em.get_epoch_id(&block_hash).unwrap();
                let shard_uid = shard_id_to_uid(em, shard_id, &epoch_id).unwrap();
                let span = tracing::debug_span!("d3ttn");
                let prev_root = new_chunk_data.prev_state_root;
                let res = if flat {
                    apply_new_chunk(
                        ApplyChunkReason::ValidateChunkStateWitness,
                        &span,
                        new_chunk_data,
                        ShardContext { shard_uid, should_apply_chunk: true },
                        client.runtime_adapter.as_ref(),
                        MaybePinnedMemtrieRoot::no_memtries(),
                        None,
                    )
                    .map(|r| r.apply_result)
                    .map_err(|e| format!("{e:?}"))
                } else {
                    let NewChunkData {
                        gas_limit, prev_state_root, prev_validator_proposals, transactions, block, receipts,
                        storage_context, ..
                    } = new_chunk_data;
                    assert!(matches!(storage_context.storage_data_source, StorageDataSource::Recorded(_)));
                    client
                        .runtime_adapter
                        .apply_chunk(
                            RuntimeStorageConfig {
                                state_root: prev_state_root,
                                use_flat_storage: false,
                                source: storage_context.storage_data_source,
                                state_patch: storage_context.state_patch,
                            },
                            ApplyChunkReason::ValidateChunkStateWitness,
                            ApplyChunkShardContext {
                                shard_uid,
                                last_validator_proposals: ValidatorStakeIter::new(&prev_validator_proposals),
                                gas_limit,
                                is_new_chunk: true,
                                on_post_state_ready: None,
                                memtrie_pin: MaybePinnedMemtrieRoot::no_memtries(),
                            },
                            block,
                            &receipts,
                            transactions,
                        )
                        .map_err(|e| format!("{e:?}"))
                };
                Some((block_hash, shard_id, shard_uid, res, prev_root))
            };
            let Some((bh, shard_id, shard_uid, v, prev_root)) = apply(true) else { continue };
            let v = v.expect("validator application of an honest witness failed");
            // the ablation's different gas can change control flow and need nodes the witness does
            // not record: a storage error there counts as a differing chunk (validator would reject)
            let a = match apply(false).unwrap().3 {
                Ok(a) => Some(a),
                Err(e) => {
                    t.ablation_storage_errors += 1;
                    eprintln!("ablation apply failed (counted as a differing chunk): {e}");
                    None
                }
            };
            if let Some(tw) = trace.as_mut() {
                for o in &v.outcomes {
                    if let Some(c) = calls_by_tx.get(&o.id) {
                        if let Some(r) = o.outcome.receipt_ids.first() {
                            calls_by_receipt.insert(*r, c.clone());
                        }
                    }
                }
                if !write_trace(tw, &sw, prev_root, &v, &calls_by_receipt) {
                    trace_skipped += 1;
                }
            }
            t.chunks += 1;
            if !v.outcomes.is_empty() {
                t.chunks_with_outcomes += 1;
            }
            // P: the outcomes the producer stored when it applied this chunk
            let store = client.chain.chain_store();
            let producer_memtrie = client.runtime_adapter.get_tries().get_memtries(shard_uid).is_some();
            if producer_memtrie {
                t.memtrie_producers += 1;
            }
            let extra = store.get_chunk_extra(&bh, &shard_uid).unwrap();
            if extra.gas_used() != v.total_gas_burnt {
                t.chunk_gas_diff += 1;
                eprintln!("chunk gas differs at {bh} {shard_id}: P {:?} V {:?}", extra.gas_used(), v.total_gas_burnt);
            }
            let mut chunk_a_diff = false;
            let mut digest = Vec::new();
            for (i, vo) in v.outcomes.iter().enumerate() {
                t.outcomes += 1;
                let po = store
                    .get_outcomes_by_id(&vo.id)
                    .unwrap()
                    .into_iter()
                    .find(|x| x.block_hash == bh)
                    .map(|x| x.outcome_with_id);
                match &po {
                    None => {
                        t.p_missing += 1;
                        eprintln!("producer has no stored outcome for {} at {bh}", vo.id);
                    }
                    Some(po) => {
                        if outcome_bytes(po) != outcome_bytes(vo) {
                            t.p_vs_v_diff += 1;
                            eprintln!("P/V outcome differs {}:\n P {:?}\n V {:?}", vo.id, po.outcome, vo.outcome);
                        }
                    }
                }
                let ttn = profile_gas(&vo.outcome.metadata, ExtCosts::touching_trie_node);
                let cached = profile_gas(&vo.outcome.metadata, ExtCosts::read_cached_trie_node);
                if ttn + cached > 0 {
                    t.fn_outcomes_with_ttn += 1;
                }
                t.ttn_gas_v += ttn as u128;
                t.cached_gas_v += cached as u128;
                if let Some(ao) = a.as_ref().and_then(|a| a.outcomes.get(i)) {
                    t.ttn_gas_a += profile_gas(&ao.outcome.metadata, ExtCosts::touching_trie_node) as u128;
                    t.cached_gas_a += profile_gas(&ao.outcome.metadata, ExtCosts::read_cached_trie_node) as u128;
                    if outcome_bytes(ao) != outcome_bytes(vo) {
                        t.a_diff_outcomes += 1;
                        chunk_a_diff = true;
                    }
                    if ao.outcome.compute_usage != vo.outcome.compute_usage {
                        t.compute_v_vs_a_diff += 1;
                    }
                } else {
                    chunk_a_diff = true;
                }
                digest.push(json!({
                    "id": vo.id.to_string(),
                    "gas": vo.outcome.gas_burnt.as_gas(),
                    "compute": vo.outcome.compute_usage,
                    "ttn": ttn, "cached": cached,
                    "h": hash(&outcome_bytes(vo)).to_string(),
                }));
            }
            if a.as_ref().map_or(true, |a| a.outcomes.len() != v.outcomes.len() || a.new_root != v.new_root) {
                chunk_a_diff = true;
            }
            if chunk_a_diff {
                t.a_diff_chunks += 1;
            }
            digests.push(json!({
                "block": bh.to_string(), "shard": shard_id.to_string(),
                "producer_memtrie": producer_memtrie,
                "new_root": v.new_root.to_string(),
                "gas": v.total_gas_burnt.as_gas(),
                "outcomes": digest,
            }));
        }
    }
    let summary = json!({
        "seed": p.seed, "n_shards": p.n_shards, "blocks": p.blocks, "memtries": p.memtries,
        "chunks": t.chunks, "chunks_with_outcomes": t.chunks_with_outcomes, "outcomes": t.outcomes,
        "outcomes_with_trie_node_charges": t.fn_outcomes_with_ttn,
        "producer_vs_validator_outcome_diffs": t.p_vs_v_diff,
        "producer_outcome_missing": t.p_missing,
        "chunk_gas_diffs": t.chunk_gas_diff,
        "producer_memtrie_chunks": t.memtrie_producers,
        "judge_ok": t.judge_ok, "judge_fail": t.judge_fail,
        "validator_ttn_gas": t.ttn_gas_v.to_string(), "validator_cached_gas": t.cached_gas_v.to_string(),
        "ablation_ttn_gas": t.ttn_gas_a.to_string(), "ablation_cached_gas": t.cached_gas_a.to_string(),
        "ablation_outcome_diffs": t.a_diff_outcomes, "ablation_chunk_diffs": t.a_diff_chunks,
        "ablation_compute_diffs": t.compute_v_vs_a_diff,
        "trace_chunks_skipped": trace_skipped,
        "ablation_storage_errors": t.ablation_storage_errors,
    });
    println!("{}", serde_json::to_string_pretty(&summary).unwrap());
    std::fs::write(out, serde_json::to_string_pretty(&json!({"summary": summary, "chunks": digests})).unwrap())
        .unwrap();
}
