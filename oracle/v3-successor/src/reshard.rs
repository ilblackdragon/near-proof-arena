//! Real shard-split fixtures (`reshard` command, workplan W11).
//!
//! The D3 chain loop (oracle/v3-d3/src/chaind3.rs `run_chain_d3`, unchanged there) with a shard
//! layout change scheduled the way the pinned nearcore schedules one at PV86: **dynamic
//! resharding** (`ProtocolFeature::DynamicResharding`, stable at PV85,
//! core/primitives-core/src/version.rs:564,575). nearcore requires a static layout for the genesis
//! epoch (chain/epoch-manager/src/genesis.rs:64-69), so the genesis runs PV85 with the static
//! layout, every client votes PV86 (the binary's `PROTOCOL_VERSION`, immediate voting for a local
//! chain id), and the PV86 epoch config is the same config with
//! `ShardLayoutConfig::Dynamic { force_split_shards: [parent] }` — the construction of the pinned
//! test `build_epoch_config_store` (test-loop-tests/src/tests/resharding_v3.rs:516-545).
//!
//! What then happens is nearcore's own path, nothing here forges it:
//! * in the first PV86 epoch (N), the chunk producer of the parent computes `proposed_split`
//!   (`compute_proposed_split`, chain/chain/src/runtime/mod.rs:583-621, a `find_trie_split` over the
//!   memtrie) for chunks possibly last in the epoch; the block producer puts the selected split in
//!   the last block's `shard_split` (`get_upcoming_shard_split`, chain/epoch-manager/src/lib.rs:1919);
//! * `finalize_epoch` derives the V3 layout of epoch N+2 (`next_next_shard_layout`, lib.rs:679-745);
//! * the last block of N+1 is the resharding block: `ReshardingManager::split_shard` builds both
//!   children from the parent memtrie (chain/chain/src/resharding/manager.rs:107-295, memtries are
//!   required, so the runtimes here load memtries for tracked shards and every client tracks all
//!   shards);
//! * the first child chunks' witnesses carry `ImplicitTransitionParams::Resharding` (Left/Right),
//!   checked by `validate_chunk_state_witness_impl` (chunk_validation.rs:702-733).
//!
//! Every captured witness is judged by the cold validator (src/d3judge.rs, as the D3 corpus) and
//! written with nearcore's own pre-validation of its implicit transitions in the metadata. The D3
//! classifier is not used: its main-transition shard lookup assumes no resharding
//! (oracle/v3/src/d0.rs:115-118). Mutants: a corrupted child post-state root, a dropped parent-trie
//! node of the split transition (both judged by nearcore), and two claim layout facts (the child
//! epoch's layout replaced by the parent layout, or derived with a different boundary account;
//! nearcore does not read claim facts, so these are claim-v3 discipline rejects).

use crate::chaingen::{ChainParams, Setup};
use crate::claim::build_claim;
use crate::d3judge::ColdJudge;
use crate::enc::{Claim, encode_witness};
use integration_tests::env::test_env::TestEnv;
use near_chain::{ChainStoreAccess, Provenance};
use near_chain::chain::ChunkStateWitnessMessage;
use near_chain::runtime::NightshadeRuntime;
use near_chain::stateless_validation::chunk_validation::{ImplicitTransitionParams, MainTransition};
use near_chain::stateless_validation::processing_tracker::ProcessingDoneTracker;
use near_chain_configs::{DEFAULT_GC_NUM_EPOCHS_TO_KEEP, Genesis, GenesisConfig, GenesisRecords};
use near_epoch_manager::{EpochManager, EpochManagerHandle};
use near_parameters::RuntimeConfigStore;
use near_primitives::account::{AccessKey, AccountContract};
use near_primitives::action::{Action, TransferAction};
use near_primitives::epoch_manager::{DynamicReshardingConfig, EpochConfig, EpochConfigStore, ShardLayoutConfig};
use near_primitives::hash::CryptoHash;
use near_primitives::num_rational::Rational32;
use near_primitives::shard_layout::ShardLayout;
use near_primitives::sharding::{ShardChunkHeader, ShardChunkHeaderV3};
use near_primitives::state::PartialState;
use near_primitives::trie_split::TrieSplit;
use near_primitives::state_record::StateRecord;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::test_utils::create_test_signer;
use near_primitives::transaction::SignedTransaction;
use near_primitives::types::{AccountId, AccountInfo, Balance, Gas, ShardId};
use near_primitives::version::PROTOCOL_VERSION;
use near_primitives_core::account::Account;
use near_store::TrieConfig;
use near_store::genesis::initialize_genesis_state;
use near_store::test_utils::create_test_store;
use near_store::trie::ops::resharding::RetainMode;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use serde_json::json;
use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::sync::Arc;

const ACCTS_PER_SHARD: usize = 10;

fn acct(k: usize, j: usize) -> AccountId {
    format!("s{k}a{j:02}").parse().unwrap()
}

#[derive(Clone, Debug)]
pub struct ReshardParams {
    pub base: ChainParams,
    /// index k of the shard to split (the shard of `s{k}a00`)
    pub split_k: usize,
    /// 0: plain; 1: the parent's chunk of the resharding block is missing; 2: the children's
    /// chunks of the first block after the resharding block are missing
    pub variant: usize,
    pub max_txs: usize,
    pub max_d3: usize,
    pub p_contract: f64,
    /// burst probability per shard and height while the split is scheduled (hot window)
    pub p_burst_hot: f64,
    pub min_gas_price: u128,
    /// a second forced split: this shard id is added to `force_split_shards` (a child of the
    /// first split, so the child splits again once `min_epochs_between_resharding` allows)
    pub second_split: Option<u64>,
    /// `max_number_of_shards` (default: one split, or two with `second_split`)
    pub max_shards: Option<u64>,
    /// force the split of the shard of `s{split_k}a00` (`false`: thresholds decide)
    pub force: bool,
    pub mem_threshold: u64,
    pub min_child: u64,
    /// `(shard id, epochs)`: from the first block of the first post-split epoch, that shard's
    /// chunks are not produced for this many epochs (a boundary walk across several epochs)
    pub starve: Option<(u64, u64)>,
    /// storage-limit composition: the parent's chunk of the resharding block runs a receipt
    /// above `per_receipt_storage_proof_size_limit` and one past the chunk soft limit
    pub zlim: bool,
    /// per hot height: probability of a global-contract deployment (distribution receipts
    /// through congested shards across the split)
    pub p_global_hot: f64,
}

/// The storage-limit composition account of the split shard (`zlim`).
fn zlim_acct(k: usize) -> AccountId {
    format!("s{k}zlim").parse().unwrap()
}

/// `zlim` value sizes: `big` alone stays below the per-receipt limit (4,000,000 B), `big` and
/// `pad2` together exceed it.
const ZLIM_BIG: usize = 3_950_000;
const ZLIM_PAD2: usize = 100_000;

/// `chaind3::setup_d3` with the genesis at PV85 (static layout), a PV86 epoch config that forces
/// a split of the shard of `s{split_k}a00`, memtries loaded for tracked shards, and every client
/// tracking every shard.
pub fn setup_reshard(rp: &ReshardParams) -> Setup {
    let p = &rp.base;
    let accounts: Vec<Vec<AccountId>> = (0..p.n_shards).map(|k| (0..ACCTS_PER_SHARD).map(|j| acct(k, j)).collect()).collect();
    let boundaries: Vec<AccountId> = (1..p.n_shards).map(|k| format!("s{k}").parse().unwrap()).collect();
    let shard_layout = ShardLayout::multi_shard_custom(boundaries, 3);
    let validators = crate::chaind2::validators_of(p.n_shards);
    let initial_balance = Balance::from_near(1_000_000);
    let validator_stake = Balance::from_near(1_000_000);
    let min_gas_price = rp.min_gas_price;
    let genesis_pv = PROTOCOL_VERSION - 1;
    let mut genesis_config = GenesisConfig {
        protocol_version: genesis_pv,
        genesis_height: 10000,
        genesis_time: chrono::DateTime::from_timestamp(1_700_000_000, 0).unwrap(),
        chain_id: "arena-v3-local".to_string(),
        shard_layout: shard_layout.clone(),
        validators: validators
            .iter()
            .map(|a| AccountInfo { account_id: a.clone(), public_key: create_test_signer(a.as_str()).public_key(), amount: validator_stake })
            .collect(),
        epoch_length: p.epoch_length,
        transaction_validity_period: 50.min(2 * p.epoch_length),
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
        min_gas_price: Balance::from_yoctonear(min_gas_price),
        max_gas_price: Balance::from_yoctonear(if min_gas_price > 0 { 10u128.pow(22) } else { 0 }),
        ..Default::default()
    };
    let mut records = Vec::new();
    for a in accounts.iter().flatten() {
        let staked = if validators.contains(a) { validator_stake } else { Balance::ZERO };
        records.push(StateRecord::Account { account_id: a.clone(), account: Account::new(initial_balance, staked, AccountContract::None, 0) });
        records.push(StateRecord::access_key(a.clone(), &create_test_signer(a.as_str()).public_key(), AccessKey::full_access()));
        genesis_config.total_supply = genesis_config.total_supply.checked_add(initial_balance).unwrap().checked_add(staked).unwrap();
    }
    let (extra, supply) = crate::d2gen::genesis_records(&accounts);
    records.extend(extra);
    genesis_config.total_supply = genesis_config.total_supply.checked_add(supply).unwrap();
    let (extra3, supply3) = crate::d3gen::genesis_records(&accounts);
    records.extend(extra3);
    genesis_config.total_supply = genesis_config.total_supply.checked_add(supply3).unwrap();
    if rp.zlim {
        let a = zlim_acct(rp.split_k);
        let slim = crate::scenarios::slim_wasm();
        let amount = Balance::from_near(1_000_000);
        records.push(StateRecord::Account { account_id: a.clone(), account: Account::new(amount, Balance::ZERO, AccountContract::Local(CryptoHash::hash_bytes(slim)), 0) });
        records.push(StateRecord::access_key(a.clone(), &create_test_signer(a.as_str()).public_key(), AccessKey::full_access()));
        records.push(StateRecord::Contract { account_id: a.clone(), code: slim.to_vec() });
        for (k, v) in [(b"big".to_vec(), vec![0xB1u8; ZLIM_BIG]), (b"pad2".to_vec(), vec![0xC1; ZLIM_PAD2]), (b"x".to_vec(), vec![0x58; 100])] {
            records.push(StateRecord::Data { account_id: a.clone(), data_key: k.into(), value: v.into() });
        }
        genesis_config.total_supply = genesis_config.total_supply.checked_add(amount).unwrap();
    }
    let genesis = Genesis::new(genesis_config, GenesisRecords(records)).unwrap();
    let mut clients = validators.clone();
    clients.extend(crate::chaind2::stakers_of());
    let n = clients.len();
    let stores: Vec<_> = (0..n).map(|_| create_test_store()).collect();
    let mut base: EpochConfig = (&genesis.config).into();
    base.block_producer_kickout_threshold = 0;
    base.chunk_producer_kickout_threshold = 0;
    let parent = shard_layout.account_id_to_shard_id(&accounts[rp.split_k][0]);
    let mut force_split_shards = if rp.force { vec![parent] } else { vec![] };
    force_split_shards.extend(rp.second_split.map(ShardId::new));
    let max_number_of_shards = rp.max_shards.unwrap_or(p.n_shards as u64 + if rp.second_split.is_some() { 2 } else { 1 });
    let mut dynamic = base.clone();
    if rp.second_split.is_some() {
        // keep each shard's chunk producers from epoch to epoch, so the producers of a re-split
        // child are among the producers of its parent and hold its state (TestEnv has no state
        // sync); the split itself distributes them (StickyReshardingValidatorAssignment)
        dynamic.chunk_producer_assignment_changes_limit = 0;
    }
    dynamic.shard_layout_config = ShardLayoutConfig::Dynamic {
        dynamic_resharding_config: DynamicReshardingConfig {
            memory_usage_threshold: rp.mem_threshold,
            min_child_memory_usage: rp.min_child,
            max_number_of_shards,
            min_epochs_between_resharding: 1.try_into().unwrap(),
            force_split_shards,
            block_split_shards: vec![],
        },
    };
    let ecs = EpochConfigStore::test(BTreeMap::from_iter(vec![(genesis_pv, Arc::new(base)), (PROTOCOL_VERSION, Arc::new(dynamic))]));
    let ems: Vec<Arc<EpochManagerHandle>> =
        stores.iter().map(|s| EpochManager::new_arc_handle_from_epoch_config_store(s.clone(), &genesis.config, ecs.clone())).collect();
    let clock = near_time::FakeClock::new(near_time::Utc::from_unix_timestamp(1_700_000_000).unwrap());
    let trie_config = TrieConfig { load_memtries_for_tracked_shards: true, ..TrieConfig::default() };
    let g = genesis.clone();
    let env = TestEnv::builder(&genesis.config)
        .clock(clock.clock())
        .clients(clients)
        .stores(stores)
        .epoch_managers(ems.clone())
        .maybe_track_all_shards(std::env::var("RESHARD_TRACK_ALL").is_ok())
        .save_tx_outcomes(true)
        .internal_initialize_nightshade_runtimes(vec![RuntimeConfigStore::new(None); n], vec![trie_config; n], move |home, store, cache, em, rcs, tc| {
            initialize_genesis_state(store.clone(), &g, Some(home.as_path()));
            NightshadeRuntime::test_with_trie_config(&home, store, cache, &g.config, em, Some(rcs), tc, DEFAULT_GC_NUM_EPOCHS_TO_KEEP, false, 1, false)
        })
        .build();
    let wasm_config = RuntimeConfigStore::new(None).get_config(PROTOCOL_VERSION).wasm_config.clone();
    for c in &env.clients {
        let cache = c.runtime_adapter.compiled_contract_cache();
        for (_, code) in crate::d3contracts::all().into_iter().chain(extra_codes(rp)) {
            let code = near_vm_runner::ContractCode::new(code, None);
            near_vm_runner::precompile_contract(&code, Arc::clone(&wasm_config), Some(cache)).expect("cache").expect("compile");
        }
    }
    Setup { clock, env, ems, genesis, accounts }
}

/// `process_shards_manager_responses_and_finish_processing_blocks`, optionally without producing the
/// next chunks. A client tracking every shard often finishes a block only here (once the requested
/// parts arrive), so a forced or random missing chunk must also be honoured here.
fn finish_processing(env: &mut TestEnv, j: usize, produce: bool) {
    if produce {
        env.process_shards_manager_responses_and_finish_processing_blocks(j);
        return;
    }
    loop {
        env.process_shards_manager_responses(j);
        let mut accepted = Vec::new();
        while near_chain::test_utils::wait_for_all_blocks_in_processing(&env.clients[j].chain) {
            accepted.extend(env.clients[j].postprocess_ready_blocks(None, false).0);
        }
        if accepted.is_empty() {
            return;
        }
    }
}

/// Contracts of the reshard-only compositions (appended as witness code blobs like the registry's).
fn extra_codes(rp: &ReshardParams) -> Vec<(&'static str, Vec<u8>)> {
    if rp.zlim { vec![("slim", crate::scenarios::slim_wasm().to_vec())] } else { vec![] }
}

#[derive(Default)]
pub struct ReshardStats {
    pub honest: usize,
    pub honest_ok: usize,
    pub mutants: usize,
    pub shapes: BTreeMap<String, usize>,
    pub boundary: Vec<serde_json::Value>,
    /// gate.no_split cases given a forged proposed split so far, per chain
    pub forged_gate: BTreeMap<usize, usize>,
}

fn hex32(h: &[u8]) -> String {
    hex::encode(h)
}

/// The boundary shape of a witness, from nearcore's own pre-validation and the claim.
fn shape_of(kinds: &[serde_json::Value], pvs: &[u32], layouts_differ: bool, gate: bool, proposed: bool, next_layout_differs: bool) -> String {
    let split = kinds.iter().find_map(|k| k.get("resharding").and_then(|r| r.get("retain")).and_then(|x| x.as_str()).map(str::to_string));
    if pvs.iter().any(|v| *v != 86) {
        return "pv85".into();
    }
    if let Some(m) = split {
        return format!("split.{m}");
    }
    if proposed {
        return "gate.proposed_split".into();
    }
    if gate {
        return "gate.no_split".into();
    }
    if layouts_differ {
        return "cross_layout.no_split".into();
    }
    if next_layout_differs {
        return "pre_split".into();
    }
    "plain".into()
}

/// Run one chain; write `out/cases/<chain>-h<height>-s<shard>` and `out/mutants/...`.
pub fn run_chain_reshard(chain_idx: usize, rp: &ReshardParams, out: &Path, st: &mut ReshardStats) {
    let p = &rp.base;
    let mut s = setup_reshard(rp);
    let cold_home = out.join(format!(".cold-{chain_idx}"));
    let judge = ColdJudge::new(&s.env.clients, &s.ems, &s.genesis, &cold_home);
    // W01 (opt-in): nearcore's per-outcome observables of every honest witness; no RNG use
    let mut obs = crate::observables::enabled()
        .then(|| crate::observables::Collector::new(&s.env.clients, &s.ems, &s.genesis, &cold_home, out, chain_idx));
    let mut world = crate::d2gen::World::new(&s.accounts, crate::chaind2::validators_of(p.n_shards), crate::chaind2::stakers_of());
    let mut w3 = crate::d3gen::D3World::new(p.n_shards);
    let mut labels: HashMap<CryptoHash, String> = HashMap::new();
    let mut rng = StdRng::seed_from_u64(p.seed);
    let reg = crate::d3contracts::registry();
    let tip0 = s.env.clients[0].chain.head().unwrap();
    let mut height = tip0.height;
    let mut starve_from: Option<u64> = None;
    let track_all = std::env::var("RESHARD_TRACK_ALL").is_ok();
    let mut tracked: Vec<(String, CryptoHash)> = Vec::new();
    let mut zlim_sent = false;
    let extra: HashMap<CryptoHash, Vec<u8>> = extra_codes(rp).into_iter().map(|(_, c)| (CryptoHash::hash_bytes(&c), c)).collect();
    for round in 0..p.blocks {
        height += 1;
        s.clock.advance(near_time::Duration::milliseconds(1100));
        let tip = s.env.clients[0].chain.head().unwrap();
        let (cur_layout, next_layout, epoch_start, cur_pv) = {
            let em = &s.env.clients[0].epoch_manager;
            let eid = em.get_epoch_id_from_prev_block(&tip.last_block_hash).unwrap();
            let neid = em.get_next_epoch_id_from_prev_block(&tip.last_block_hash).unwrap();
            let start = em.get_epoch_start_from_epoch_id(&eid).unwrap_or(0);
            (em.get_shard_layout(&eid).unwrap(), em.get_shard_layout(&neid).unwrap(), start, em.get_epoch_protocol_version(&eid).unwrap())
        };
        {
            let em = s.ems[0].read();
            world.minimum_stake = em.minimum_stake(&tip.last_block_hash).map(|b| b.as_yoctonear()).unwrap_or(0);
        }
        let split_scheduled = next_layout != cur_layout;
        // hot window: the epoch before a split and the first blocks of every post-split epoch
        let after_split = cur_layout.num_shards() as usize > p.n_shards && height < epoch_start + 4;
        let hot = split_scheduled || (after_split && cur_pv == 86 && round > 0);
        if std::env::var("D3_TRACE").is_ok() {
            eprintln!("round {round} height {height} pv {cur_pv} shards {} next {} hot {hot}", cur_layout.num_shards(), next_layout.num_shards());
        }
        // the shard the scheduled split removes
        let parent_sid = if split_scheduled { cur_layout.shard_ids().find(|x| !next_layout.shard_ids().any(|y| y == *x)) } else { None };
        let last_of_epoch = epoch_start + p.epoch_length - 1;
        if split_scheduled && height == last_of_epoch && starve_from.is_none() {
            starve_from = Some(height + 1);
        }
        // ---- honest transactions: D2 + D3 traffic; in the hot window, every shard bursts into a
        // sink shard `T = split_k + 1` (congesting it, so that senders, the parent among them,
        // buffer outgoing receipts) and `T` bursts into the parent (delayed receipts)
        let sink = (rp.split_k + 1) % p.n_shards;
        let mut txs: Vec<(String, SignedTransaction)> = Vec::new();
        for k in 0..p.n_shards {
            let p_burst = if hot { rp.p_burst_hot } else { p.p_burst };
            if !rng.gen_bool(p.p_tx_shard.max(if hot { 0.9 } else { 0.0 })) {
                continue;
            }
            // zlim: the parent's own chunks around the resharding block stay below the gas limit,
            // so the storage-limit receipts run in the parent's last chunk
            let zlim_quiet = rp.zlim && split_scheduled && k == rp.split_k && height + 4 >= last_of_epoch;
            if rng.gen_bool(p_burst) && !zlim_quiet {
                let n = rng.gen_range(300..700);
                let tgt = if !hot { (k + rng.gen_range(1..p.n_shards)) % p.n_shards } else if k == sink { rp.split_k } else { sink };
                for _ in 0..n {
                    let signer_id = s.accounts[k][rng.gen_range(0..crate::d2gen::HONEST)].clone();
                    let r = s.accounts[tgt][rng.gen_range(0..ACCTS_PER_SHARD)].clone();
                    let dep = rng.gen_range(1..10u128.pow(22));
                    let Some(t) = world.plain_tx(&s, &tip.last_block_hash, &signer_id, &r, vec![Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(dep) })]) else { continue };
                    txs.push(("h.burst".into(), t));
                }
            } else {
                let n = rng.gen_range(1..=rp.max_txs);
                world.yield_bias = false;
                txs.extend(world.gen_txs(&s, &tip.last_block_hash, height, &mut rng, n, rp.p_contract));
                let m = rng.gen_range(0..=rp.max_d3);
                for _ in 0..m {
                    if let Some(x) = w3.one(&mut world, &s, &tip.last_block_hash, height, &mut rng) {
                        txs.push(x);
                    }
                }
            }
        }
        // ---- global-contract deployments in the hot window: their distribution receipts walk
        // every shard and are buffered/delayed by the congestion the bursts cause
        if rp.p_global_hot > 0.0 && hot && rng.gen_bool(rp.p_global_hot) {
            let k = rng.gen_range(0..p.n_shards);
            let signer_id = s.accounts[k][rng.gen_range(0..crate::d2gen::HONEST)].clone();
            let deploy = Action::DeployGlobalContract(near_primitives::action::DeployGlobalContractAction {
                code: crate::d3contracts::TINY.to_vec().into(),
                deploy_mode: near_primitives::action::GlobalContractDeployMode::CodeHash,
            });
            if let Some(t) = world.plain_tx(&s, &tip.last_block_hash, &signer_id, &signer_id, vec![deploy]) {
                txs.push(("h.reshard_global_deploy".into(), t));
            }
        }
        // ---- storage-limit composition: in the parent's chunk of the resharding block, a receipt
        // above the per-receipt storage-proof limit, then one the chunk soft limit postpones
        if rp.zlim && split_scheduled && height + 1 == last_of_epoch && !zlim_sent {
            zlim_sent = true;
            let a = zlim_acct(rp.split_k);
            let run = |prog: crate::scenarios::Prog| {
                Action::FunctionCall(Box::new(near_primitives::action::FunctionCallAction {
                    method_name: "run".into(),
                    args: prog.0,
                    gas: Gas::from_teragas(300),
                    deposit: Balance::ZERO,
                }))
            };
            let progs = [
                ("h.zlim_above_receipt_limit", crate::scenarios::Prog::default().r(b"big").r(b"pad2")),
                ("h.zlim_past_soft_limit", crate::scenarios::Prog::default().r(b"x")),
            ];
            for (l, prog) in progs {
                if let Some(t) = world.plain_tx(&s, &tip.last_block_hash, &a, &a, vec![run(prog)]) {
                    txs.push((l.into(), t));
                }
            }
            eprintln!("  zlim: storage-limit receipts for the chunk at height {}", height + 1);
        }
        for (l, tx) in txs {
            if l.starts_with("h.zlim") || l == "h.reshard_global_deploy" {
                tracked.push((l.clone(), tx.get_hash()));
            }
            labels.insert(tx.get_hash(), l);
            for h in &s.env.rpc_handlers {
                let _ = h.process_tx(tx.clone(), false, false);
            }
        }
        // ---- forced missing chunks at the boundary (variants 1 and 2). The chunks produced after
        // block `height` are those of height `height + 1` (offset 2 from the tip).
        let mut force_skip: Vec<AccountId> = Vec::new();
        if let (Some((sid, epochs)), Some(from)) = (rp.starve, starve_from) {
            let next = height + 1;
            if next >= from && next < from + epochs * p.epoch_length {
                // the producer of shard `sid` at height+1, in the epoch of height+1
                let em = &s.env.clients[0].epoch_manager;
                let eid = if height == last_of_epoch {
                    em.get_next_epoch_id_from_prev_block(&tip.last_block_hash).unwrap()
                } else {
                    em.get_epoch_id_from_prev_block(&tip.last_block_hash).unwrap()
                };
                let key = near_primitives::stateless_validation::ChunkProductionKey { epoch_id: eid, height_created: next, shard_id: ShardId::new(sid) };
                if let Ok(info) = em.get_chunk_producer_info(&key) {
                    force_skip.push(info.take_account_id());
                    eprintln!("  starve: skipping shard {sid} chunk at height {next}");
                }
            }
        }
        if split_scheduled && rp.variant == 1 && height + 1 == last_of_epoch {
            let sid = parent_sid.unwrap();
            force_skip.push(s.env.get_chunk_producer_at_offset(&tip, 2, sid));
            eprintln!("  variant 1: skipping parent chunk {sid} at height {}", height + 1);
        }
        if split_scheduled && rp.variant == 2 && height == last_of_epoch {
            // the chunks of height `height + 1` belong to the next (child) epoch
            let em = &s.env.clients[0].epoch_manager;
            let parent = parent_sid.unwrap();
            let neid = em.get_next_epoch_id_from_prev_block(&tip.last_block_hash).unwrap();
            for c in next_layout.get_children_shards_ids(parent).unwrap_or_default() {
                // the producer of child `c` at height+1, in the next (child) epoch
                let key = near_primitives::stateless_validation::ChunkProductionKey { epoch_id: neid, height_created: height + 1, shard_id: c };
                force_skip.push(em.get_chunk_producer_info(&key).unwrap().take_account_id());
            }
            eprintln!("  variant 2: skipping child chunks at height {}", height + 1);
        }
        // ---- block
        let bp = s.env.get_block_producer_at_offset(&tip, height - tip.height);
        if !s.env.contains_client(&bp) {
            panic!("block producer {bp} at height {height} has no client");
        }
        let block = s.env.client(&bp).produce_block(height).unwrap().unwrap();
        if let Some(split) = block.header().shard_split() {
            eprintln!("  block {height} carries shard_split {split:?}");
        }
        let mut skipped = vec![false; s.env.clients.len()];
        for i in 0..s.env.clients.len() {
            let skip = force_skip.contains(&s.env.get_client_id(i)) || rng.gen_bool(p.p_missing);
            skipped[i] = skip;
            let r = if skip {
                s.env.clients[i].process_block_test_no_produce_chunk(block.clone().into(), Provenance::NONE)
            } else {
                s.env.clients[i].process_block_test(block.clone().into(), Provenance::NONE)
            };
            match r.map(|_| ()) {
                Ok(_) => {}
                Err(near_chain::Error::ChunksMissing(_)) => {}
                Err(e) => panic!("process_block: {e:?}"),
            }
        }
        if track_all {
            // a client tracking every shard fetches the parts it does not own by request
            // (the TestEnv pattern of integration-tests/src/tests/features/in_memory_tries.rs:357-370)
            s.clock.advance(near_chunks::shards_manager_actor::CHUNK_REQUEST_SWITCH_TO_FULL_FETCH);
            for i in 0..s.env.clients.len() {
                near_async::messaging::CanSend::send(&s.env.shards_manager_adapters[i], near_chunks::test_utils::ShardsManagerResendChunkRequests);
            }
        }
        for _ in 0..4 {
            s.env.process_partial_encoded_chunks();
            for j in 0..s.env.clients.len() {
                finish_processing(&mut s.env, j, !(track_all && skipped[j]));
            }
        }
        // waiting only (no state change): a loaded machine can take longer than 8 rounds
        for _ in 0..400 {
            if s.env.clients.iter().all(|c| c.chain.head().unwrap().last_block_hash == *block.hash()) {
                break;
            }
            std::thread::sleep(std::time::Duration::from_millis(50));
            s.env.process_partial_encoded_chunks();
            for j in 0..s.env.clients.len() {
                finish_processing(&mut s.env, j, !(track_all && skipped[j]));
            }
        }
        for (ci, c) in s.env.clients.iter().enumerate() {
            assert_eq!(c.chain.head().unwrap().last_block_hash, *block.hash(), "client {ci} did not finish block {height}");
        }
        // ---- capture and deliver witnesses
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

        // ---- judge and write
        for (ci, sw, accesses) in captured {
            st.honest += 1;
            let client = &s.env.clients[ci];
            let built = match build_claim(client, &s.ems[0], &s.genesis.config, &sw) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("claim build failed: {e}");
                    continue;
                }
            };
            let codes: Vec<Vec<u8>> = accesses.iter().filter_map(|h| reg.by_hash.get(h).map(|x| x.1.clone()).or_else(|| extra.get(h).cloned())).collect();
            let wb = borsh::to_vec(&sw).unwrap();
            let rs = (built.claim.rs_data_parts, built.claim.rs_total_parts);
            if let Some(c) = obs.as_mut() {
                c.record(ci, client, &wb, &codes, &built.claim.encode(), chain_idx);
            }
            let verdict = judge.judge(ci, client, &wb, &codes, rs, None);
            if verdict.is_ok() {
                st.honest_ok += 1;
            } else {
                eprintln!("honest witness rejected by the cold validator: {verdict:?}");
            }
            write_case(chain_idx, rp, client, &judge, ci, &built, &sw, &wb, &codes, &verdict, &labels, out, st);
        }
    }
    let _ = std::fs::remove_dir_all(&cold_home);
    if !tracked.is_empty() {
        // nearcore's stored outcome tree of every composition transaction
        let v: Vec<serde_json::Value> = tracked.iter().map(|(l, h)| json!({"label": l, "tx": h.to_string(), "outcomes": outcome_tree(&s, h)})).collect();
        std::fs::write(out.join(format!("reshard-outcomes-{chain_idx:02}.json")), serde_json::to_string_pretty(&v).unwrap()).unwrap();
    }
}

/// The outcome tree of a transaction (BFS over receipt ids) from whichever client stored it.
fn outcome_tree(s: &Setup, id: &CryptoHash) -> Vec<serde_json::Value> {
    let mut out = Vec::new();
    let mut queue = std::collections::VecDeque::from([*id]);
    while let Some(id) = queue.pop_front() {
        let found = s.env.clients.iter().find_map(|c| {
            let o = c.chain.get_execution_outcome(&id).ok()?;
            let h = c.chain.get_block_header(&o.block_hash).ok()?.height();
            Some((o, h))
        });
        let Some((o, h)) = found else {
            out.push(json!({"id": id.to_string(), "executed": false}));
            continue;
        };
        let oc = &o.outcome_with_id.outcome;
        out.push(json!({"id": id.to_string(), "executed": true, "height": h, "executor": oc.executor_id.to_string(),
                        "status": format!("{:?}", oc.status), "gas_burnt": oc.gas_burnt.as_gas(),
                        "receipt_ids": oc.receipt_ids.iter().map(|r| r.to_string()).collect::<Vec<_>>()}));
        queue.extend(oc.receipt_ids.iter().copied());
    }
    out
}

fn vstr(r: &Result<(), String>) -> String {
    r.as_ref().map(|_| "ok".to_string()).unwrap_or_else(|e| e.clone())
}

fn write_dir(dir: &Path, claim: &Claim, witness: &[u8], codes: &[Vec<u8>], meta: &serde_json::Value) {
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("claim.bin"), claim.encode()).unwrap();
    std::fs::write(dir.join("witness.bin"), encode_witness(witness, codes)).unwrap();
    std::fs::write(dir.join("meta.json"), serde_json::to_string_pretty(meta).unwrap()).unwrap();
}

#[allow(clippy::too_many_arguments)]
fn write_case(
    chain_idx: usize,
    rp: &ReshardParams,
    client: &near_client::Client,
    judge: &ColdJudge,
    ci: usize,
    built: &crate::claim::Built,
    sw: &ChunkStateWitness,
    wb: &[u8],
    codes: &[Vec<u8>],
    verdict: &Result<(), String>,
    labels: &HashMap<CryptoHash, String>,
    out: &Path,
    st: &mut ReshardStats,
) {
    let em = client.epoch_manager.as_ref();
    let key = sw.chunk_production_key();
    let name = format!("{chain_idx:02}-h{}-s{}", key.height_created, key.shard_id);
    // nearcore's own reading of the witness's implicit transitions
    let mut main_out: Option<usize> = None;
    let mut main_block: Option<(CryptoHash, ShardId)> = None;
    let (kinds, main_shard, main_height): (Vec<serde_json::Value>, Option<u64>, Option<u64>) = match crate::judge::pre_validate(client, sw) {
        Ok(pre) => {
            let ks = pre
                .implicit_transition_params
                .iter()
                .map(|k| match k {
                    ImplicitTransitionParams::ApplyOldChunk(b, uid) => json!({"apply_old_chunk": {"height": b.height, "shard_uid": uid.to_string()}}),
                    ImplicitTransitionParams::Resharding(bd, mode, uid) => json!({"resharding": {
                        "boundary_account": bd.to_string(),
                        "retain": match mode { RetainMode::Left => "left", RetainMode::Right => "right" },
                        "child_shard_uid": uid.to_string()}}),
                })
                .collect();
            let (ms, mh) = match &pre.main_transition_params {
                MainTransition::NewChunk { block_hash, shard_id, .. } => {
                    main_block = Some((*block_hash, *shard_id));
                    let h = client.chain.get_block_header(block_hash).map(|h| h.height()).ok();
                    // the receipts the main transition produced (nearcore's own store)
                    main_out = client.chain.chain_store().get_outgoing_receipts(block_hash, *shard_id).ok().map(|r| r.len());
                    (Some(sid64(*shard_id)), h)
                }
                MainTransition::Genesis { .. } => (None, None),
            };
            (ks, ms, mh)
        }
        Err(e) => (vec![json!({"pre_validate_error": e})], None, None),
    };
    let pvs: Vec<u32> = built.claim.epochs.iter().map(|e| e.protocol_version).collect();
    let layouts_differ = built.claim.epochs.windows(2).any(|w| w[0].shard_layout != w[1].shard_layout);
    let gate = built.claim.apply_facts.iter().any(|f| f.split_gate.is_some());
    let header = sw.chunk_header();
    let proposed = header.proposed_split().is_some();
    let wl = em.get_shard_layout(&key.epoch_id).unwrap();
    let next_differs = em.get_next_epoch_id_from_prev_block(header.prev_block_hash()).ok().and_then(|n| em.get_shard_layout(&n).ok()).is_some_and(|n| n != wl);
    let mut distinct_layouts: Vec<&Vec<u8>> = Vec::new();
    for e in &built.claim.epochs {
        if !distinct_layouts.contains(&&e.shard_layout) {
            distinct_layouts.push(&e.shard_layout);
        }
    }
    let n_layouts = distinct_layouts.len();
    let mut shape = shape_of(&kinds, &pvs, layouts_differ, gate, proposed, next_differs);
    if n_layouts >= 3 && shape != "pv85" {
        // a boundary walk across two layout changes
        shape = format!("cross2.{shape}");
    }
    // nearcore's own split-gate inputs on the main transition's pre-state trie
    let gate_probe = if gate { main_block.and_then(|(bh, sid)| probe_gate(client, &bh, sid)) } else { None };
    let vu: Vec<serde_json::Value> = built
        .claim
        .apply_facts
        .iter()
        .map(|f| match &f.validator_update {
            Some(v) => json!({"stake_info": v.stake_info.len(), "nonzero_rewards": v.validator_rewards.iter().filter(|r| r.1 > 0).count()}),
            None => serde_json::Value::Null,
        })
        .collect();
    *st.shapes.entry(shape.clone()).or_default() += 1;
    let ci_h = header.congestion_info();
    let ChunkStateWitness::V2(v2) = sw;
    let n_receipts: usize = v2.source_receipt_proofs.values().map(|p| p.0.len()).sum();
    let lab = |t: &SignedTransaction| labels.get(&t.get_hash()).cloned().unwrap_or_else(|| "unknown".into());
    let PartialState::TrieValues(vals) = &sw.main_state_transition().base_state;
    let meta = json!({
        "case": name, "kind": "honest", "generator": "reshard", "chain_params": format!("{rp:?}"),
        "nearcore": vstr(verdict),
        "nearcore_judge": "cold validator (empty compiled-contract cache) with the appended code blobs",
        "expected_rel": verdict.is_ok(),
        "shape": shape,
        "epoch_id": hex32(&key.epoch_id.0.0),
        "height_created": key.height_created,
        "shard_id": sid64(key.shard_id),
        "witness_layout": format!("{wl:?}"),
        "claim_epoch_protocol_versions": pvs,
        "claim_layouts_differ": layouts_differ,
        "split_gate_in_apply_facts": gate,
        "proposed_split": header.proposed_split().map(|s| format!("{s:?}")),
        "implicit_transitions": kinds,
        "n_implicit_blocks": built.implicit.len(),
        "main_transition_shard": main_shard,
        "main_transition_height": main_height,
        "main_outgoing_receipts": main_out,
        "header_congestion": {
            "delayed_receipts_gas": ci_h.delayed_receipts_gas().to_string(),
            "buffered_receipts_gas": ci_h.buffered_receipts_gas().to_string(),
            "receipt_bytes": ci_h.receipt_bytes(),
            "allowed_shard": ci_h.allowed_shard(),
        },
        "bandwidth_requests_nonempty": header.bandwidth_requests().is_some_and(|b| match b { near_primitives::bandwidth_scheduler::BandwidthRequests::V1(v) => !v.requests.is_empty() }),
        "n_source_receipts": n_receipts,
        "n_transactions": sw.transactions().len(),
        "tx_labels": sw.transactions().iter().map(lab).collect::<Vec<_>>(),
        "n_new_transactions": sw.new_transactions().len(),
        "main_base_state_values": vals.len(),
        "witness_bytes": wb.len(),
        "code_blobs": codes.len(),
        "claim_distinct_layouts": n_layouts,
        "validator_updates": vu,
        "gate_probe": gate_probe.as_ref().map(|g| g.0.clone()),
    });
    let dir = out.join("cases").join(&name);
    write_dir(&dir, &built.claim, wb, codes, &meta);
    let split_idx = kinds.iter().position(|k| k.get("resharding").is_some());
    if std::env::var("RESHARD_DEBUG_IMPLICIT").is_ok() && !v2.implicit_transitions.is_empty() {
        debug_implicit(client, &name, sw, &kinds);
    }
    if shape.starts_with("split.") || shape.starts_with("gate.") || shape.starts_with("cross") {
        st.boundary.push(json!({"case": name, "shape": shape, "nearcore": vstr(verdict), "main_outgoing_receipts": main_out,
            "implicit_transitions": kinds, "proposed_split": meta["proposed_split"], "header_congestion": meta["header_congestion"],
            "n_source_receipts": n_receipts, "gate_probe": meta["gate_probe"], "validator_updates": meta["validator_updates"]}));
    }
    let shape = shape.strip_prefix("cross2.").map(str::to_string).unwrap_or(shape);
    // ---- split-gate header mutants: the endorsed header's `proposed_split` changed and re-signed
    // (nearcore's own `chunk_header_proposed_split_validation` test construction,
    // integration-tests/src/tests/features/shard_split_validation.rs:96-121)
    if verdict.is_ok() && (shape == "gate.proposed_split" || shape == "gate.no_split") {
        let forged = st.forged_gate.entry(chain_idx).or_default();
        let mut variants: Vec<(&str, Option<TrieSplit>)> = Vec::new();
        if let Some(sp) = header.proposed_split() {
            variants.push(("h.proposed_split_none", None));
            variants.push(("h.proposed_split_left_memory", Some(TrieSplit::new(sp.boundary_account.clone(), sp.left_memory + 1, sp.right_memory))));
        } else if *forged < 2 {
            *forged += 1;
            variants.push(("h.proposed_split_forged", Some(TrieSplit::new("s0a05".parse().unwrap(), 500_000, 500_000))));
        }
        // a threshold gate that did not split: the split nearcore's own `find_trie_split` gives on
        // this trie (correct boundary and memory), which only the thresholds rule out
        if header.proposed_split().is_none() && rp.mem_threshold != u64::MAX {
            if let Some((_, Some(sp))) = &gate_probe {
                variants.push(("h.proposed_split_unmet_threshold", Some(sp.clone())));
            }
        }
        let producer = em.get_chunk_producer_info(&key).map(|v| v.take_account_id()).unwrap_or_else(|_| "s0a00".parse().unwrap());
        let signer = create_test_signer(producer.as_str());
        let rs = (built.claim.rs_data_parts, built.claim.rs_total_parts);
        for (mname, split) in variants {
            let h = sw.chunk_header();
            let nh = ShardChunkHeaderV3::new(
                *h.prev_block_hash(), h.prev_state_root(), *h.prev_outcome_root(), *h.encoded_merkle_root(),
                h.encoded_length(), h.height_created(), h.shard_id(), h.prev_gas_used(), h.gas_limit(),
                h.prev_balance_burnt(), *h.prev_outgoing_receipts_root(), *h.tx_root(),
                h.prev_validator_proposals().collect(), h.congestion_info(),
                h.bandwidth_requests().cloned().unwrap_or_else(near_primitives::bandwidth_scheduler::BandwidthRequests::empty),
                split, &signer, PROTOCOL_VERSION);
            let mut c = built.claim.clone();
            c.chunk_inner = borsh::to_vec(&nh.inner).unwrap();
            let mut w = sw.clone();
            let ChunkStateWitness::V2(x) = &mut w;
            x.chunk_header = ShardChunkHeader::V3(nh);
            let b = borsh::to_vec(&w).unwrap();
            let exp = judge.judge(ci, client, &b, codes, rs, None);
            let m = json!({"case": format!("{name}-{mname}"), "kind": "mutant", "mutation": mname, "base": name,
                           "verdict_source": "nearcore(cold)", "nearcore": vstr(&exp), "expected_rel": exp.is_ok(), "shape": shape});
            write_dir(&out.join("mutants").join(format!("{name}-{mname}")), &c, &b, codes, &m);
            st.mutants += 1;
        }
    }
    // ---- mutants of the split transition and of the layout facts
    let Some(k) = split_idx.filter(|_| verdict.is_ok()) else { return };
    let rs = (built.claim.rs_data_parts, built.claim.rs_total_parts);
    let mut mutate = |mname: &str, claim: &Claim, wit: &[u8], exp: Result<(), String>, src: &str| {
        let m = json!({"case": format!("{name}-{mname}"), "kind": "mutant", "mutation": mname, "base": name,
                       "verdict_source": src, "nearcore": vstr(&exp), "expected_rel": exp.is_ok(), "shape": meta["shape"]});
        write_dir(&out.join("mutants").join(format!("{name}-{mname}")), claim, wit, codes, &m);
        st.mutants += 1;
    };
    // the child's post-state root of the split transition
    {
        let mut w = sw.clone();
        let ChunkStateWitness::V2(x) = &mut w;
        x.implicit_transitions[k].post_state_root.0[0] ^= 1;
        let b = borsh::to_vec(&w).unwrap();
        let exp = judge.judge(ci, client, &b, codes, rs, None);
        mutate("w.split_child_post_root", &built.claim, &b, exp, "nearcore(cold)");
    }
    // one parent-trie node dropped from the split transition's base state
    {
        let mut w = sw.clone();
        let ChunkStateWitness::V2(x) = &mut w;
        let PartialState::TrieValues(v) = &mut x.implicit_transitions[k].base_state;
        if !v.is_empty() {
            let i = v.len() / 2;
            v.remove(i);
            let b = borsh::to_vec(&w).unwrap();
            let exp = judge.judge(ci, client, &b, codes, rs, None);
            mutate("w.split_drop_parent_node", &built.claim, &b, exp, "nearcore(cold)");
        }
    }
    // claim layout facts: the witness epoch's layout replaced by the parent epoch's layout, or
    // derived from it with a different boundary account
    let wi = built.claim.epochs.iter().position(|e| e.epoch_id == key.epoch_id.0.0);
    let pi = built.claim.epochs.iter().position(|e| e.epoch_id != key.epoch_id.0.0 && e.shard_layout != built.claim.epochs[wi.unwrap()].shard_layout);
    if let (Some(wi), Some(pi)) = (wi, pi) {
        let mut c = built.claim.clone();
        c.epochs[wi].shard_layout = c.epochs[pi].shard_layout.clone();
        mutate("c.child_layout_is_parent", &c, wb, Err("claim-v3: the witness epoch's shard layout fact differs from the chain".into()), "claim-v3");
        let parent_layout: ShardLayout = borsh::from_slice(&built.claim.epochs[pi].shard_layout).unwrap();
        let bd = kinds[k]["resharding"]["boundary_account"].as_str().unwrap().to_string();
        let parent_sid = ShardId::new(main_shard.unwrap_or(0));
        let alt = (0..rp.base.n_shards).flat_map(|i| (0..ACCTS_PER_SHARD).map(move |j| acct(i, j))).find(|a| {
            a.as_str() != bd && parent_layout.account_id_to_shard_id(a) == parent_sid && !parent_layout.boundary_accounts().contains(a)
        });
        if let Some(alt) = alt {
            if let Ok(l2) = parent_layout.derive_v3(alt.clone(), || vec![parent_layout.clone()]) {
                let mut c = built.claim.clone();
                c.epochs[wi].shard_layout = borsh::to_vec(&l2).unwrap();
                mutate(&format!("c.child_layout_boundary({alt})"), &c, wb, Err("claim-v3: the witness epoch's shard layout fact differs from the chain".into()), "claim-v3");
            }
        }
    }
}

/// `check_dynamic_resharding`'s inputs on the pre-state trie of the main transition, read from the
/// client's store: `total_mem_usage` and `find_trie_split` (nearcore's functions,
/// core/store/src/trie/split.rs:590-620).
fn probe_gate(client: &near_client::Client, block_hash: &CryptoHash, shard_id: ShardId) -> Option<(serde_json::Value, Option<TrieSplit>)> {
    let block = client.chain.get_block(block_hash).ok()?;
    let layout = client.epoch_manager.get_shard_layout(block.header().epoch_id()).ok()?;
    let chunks = block.chunks();
    let root = chunks.iter().find(|c| c.shard_id() == shard_id)?.prev_state_root();
    let uid = near_primitives::shard_layout::ShardUId::from_shard_id_and_layout(shard_id, &layout);
    let trie = client.runtime_adapter.get_tries().get_view_trie_for_shard(uid, root);
    let mem = near_store::trie::total_mem_usage(&trie);
    let split = near_store::trie::find_trie_split(&trie);
    let v = json!({
        "shard_id": sid64(shard_id), "pre_state_root": format!("{root}"), "num_shards": layout.num_shards(),
        "total_mem_usage": mem.as_ref().ok(), "total_mem_usage_error": mem.as_ref().err().map(|e| format!("{e:?}")),
        "find_trie_split": split.as_ref().ok().map(|s| json!({"boundary_account": s.boundary_account.to_string(), "left_memory": s.left_memory, "right_memory": s.right_memory})),
        "find_trie_split_error": split.as_ref().err().map(|e| format!("{e:?}")),
    });
    Some((v, split.ok()))
}

pub fn cmd_reshard(args: &[String]) -> i32 {
    let arg = |name: &str| args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned());
    let num = |n: &str, d: u64| -> u64 { arg(n).map(|v| v.parse().unwrap_or_else(|_| panic!("{n}: not a number"))).unwrap_or(d) };
    let seed = num("--seed", 7);
    let out = std::path::PathBuf::from(arg("--out").expect("--out"));
    let chains = num("--chains", 3) as usize;
    let first = num("--first-chain", 0) as usize;
    let blocks = num("--blocks", 80);
    let n_shards = num("--shards", 4) as usize;
    let epoch_length = num("--epoch-length", 12);
    let gas = num("--gas-limit-tgas", 60);
    let split_k = num("--split-k", 0) as usize;
    let p_missing: f64 = arg("--p-missing").map(|s| s.parse().expect("--p-missing")).unwrap_or(0.05);
    let p_burst_hot: f64 = arg("--p-burst-hot").map(|s| s.parse().expect("--p-burst-hot")).unwrap_or(0.5);
    let min_gas_price: u128 = arg("--min-gas-price").map(|s| s.parse().expect("--min-gas-price")).unwrap_or(0);
    std::fs::create_dir_all(&out).unwrap();
    if std::env::var("RESHARD_LOG").is_ok() {
        near_o11y::testonly::init_test_logger();
    }
    let mut st = ReshardStats::default();
    let mut params = Vec::new();
    for i in first..first + chains {
        let rp = ReshardParams {
            base: ChainParams {
                seed: seed.wrapping_mul(1_000_003).wrapping_add(i as u64),
                n_shards,
                seats: 8,
                gas_limit_tgas: gas,
                epoch_length,
                blocks,
                p_missing,
                p_tx_shard: 0.5,
                p_burst: 0.03,
                p_fail: 0.0,
                p_implicit: 0.0,
                p_two: 0.0,
                long_skip: None,
            },
            split_k,
            variant: num("--variant", i as u64 % 3) as usize,
            max_txs: 4,
            max_d3: 2,
            p_contract: 0.04,
            p_burst_hot,
            min_gas_price,
            second_split: arg("--second-split").map(|v| v.parse().expect("--second-split")),
            max_shards: arg("--max-shards").map(|v| v.parse().expect("--max-shards")),
            force: !args.iter().any(|a| a == "--no-force"),
            mem_threshold: num("--mem-threshold", u64::MAX),
            min_child: num("--min-child", u64::MAX),
            starve: arg("--starve").map(|v| {
                let (a, b) = v.split_once(':').expect("--starve SHARD:EPOCHS");
                (a.parse().expect("--starve shard"), b.parse().expect("--starve epochs"))
            }),
            zlim: args.iter().any(|a| a == "--zlim"),
            p_global_hot: arg("--p-global-hot").map(|s| s.parse().expect("--p-global-hot")).unwrap_or(0.0),
        };
        eprintln!("chain {i}: {rp:?}");
        params.push(format!("{rp:?}"));
        run_chain_reshard(i, &rp, &out, &mut st);
        eprintln!("  honest={} cold_ok={} mutants={} shapes={:?}", st.honest, st.honest_ok, st.mutants, st.shapes);
    }
    let summary = json!({
        "nearcore_commit": crate::NEARCORE_COMMIT, "generator": "reshard", "seed": seed, "chains": params,
        "honest_witnesses": st.honest, "honest_accepted_by_nearcore": st.honest_ok, "mutants": st.mutants,
        "shapes": st.shapes, "boundary_cases": st.boundary,
    });
    std::fs::write(out.join("summary.json"), serde_json::to_string_pretty(&summary).unwrap()).unwrap();
    if st.honest_ok != st.honest {
        eprintln!("WARNING: some honest witnesses were rejected by the cold validator");
        return 1;
    }
    0
}

fn sid64(s: ShardId) -> u64 {
    s.into()
}

/// Debug aid (`RESHARD_DEBUG_IMPLICIT`): the trie key/value differences of every implicit
/// transition, read from the client's own store (pre root = the previous transition's post root).
fn debug_implicit(client: &near_client::Client, name: &str, sw: &ChunkStateWitness, kinds: &[serde_json::Value]) {
    let ChunkStateWitness::V2(v2) = sw;
    let tries = client.runtime_adapter.get_tries();
    let mut pre = v2.main_state_transition.post_state_root;
    for (i, t) in v2.implicit_transitions.iter().enumerate() {
        let uid_s = kinds.get(i).and_then(|k| k.get("apply_old_chunk").or_else(|| k.get("resharding"))).and_then(|k| k.get("shard_uid").or_else(|| k.get("child_shard_uid"))).and_then(|x| x.as_str()).unwrap_or("");
        let Ok(uid) = uid_s.parse::<near_primitives::shard_layout::ShardUId>() else { eprintln!("DEBUG {name} #{i}: uid {uid_s}"); continue };
        let dump = |root: CryptoHash, uid| -> BTreeMap<Vec<u8>, Vec<u8>> {
            let trie = tries.get_trie_for_shard(uid, root);
            match trie.disk_iter() {
                Ok(it) => it.filter_map(|x| x.ok()).map(|(k, v)| (k, v)).collect(),
                Err(e) => { eprintln!("DEBUG {name}: iter {e:?}"); BTreeMap::new() }
            }
        };
        let a = dump(pre, uid);
        let b = dump(t.post_state_root, uid);
        for (k, v) in &b {
            if a.get(k) != Some(v) {
                eprintln!("DEBUG {name} #{i} {uid_s} set {} = {}", hex::encode(k), hex::encode(&v[..v.len().min(400)]));
            }
        }
        for k in a.keys() {
            if !b.contains_key(k) {
                eprintln!("DEBUG {name} #{i} {uid_s} del {}", hex::encode(k));
            }
        }
        pre = t.post_state_root;
    }
}
