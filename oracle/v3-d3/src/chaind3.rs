//! Domain-D3 chain generation (`gen --domain d3`): the D2 chain loop (oracle/v3-d1/src/
//! chaind2.rs, unchanged there) with the D3 genesis contracts (src/d3gen.rs), D3 honest
//! traffic mixed into the D2 traffic, the contract-access sets of every produced witness
//! (`DistributeStateWitnessRequest::contract_updates`), and a cold validator as the judge
//! (src/d3judge.rs) with the needed code blobs appended (src/d3.rs writes the cases).

use crate::chaingen::{ChainParams, GenOpts, Setup, Stats};
use crate::claim::build_claim;
use integration_tests::env::nightshade_setup::TestEnvNightshadeSetupExt;
use integration_tests::env::test_env::TestEnv;
use near_chain::Provenance;
use near_chain::chain::ChunkStateWitnessMessage;
use near_chain::stateless_validation::processing_tracker::ProcessingDoneTracker;
use near_chain_configs::{Genesis, GenesisConfig, GenesisRecords};
use near_crypto::InMemorySigner;
use near_epoch_manager::{EpochManager, EpochManagerHandle};
use near_parameters::RuntimeConfigStore;
use near_primitives::account::{AccessKey, AccountContract};
use near_primitives::action::{Action, TransferAction};
use near_primitives::epoch_manager::{EpochConfig, EpochConfigStore};
use near_primitives::hash::CryptoHash;
use near_primitives::num_rational::Rational32;
use near_primitives::shard_layout::ShardLayout;
use near_primitives::state_record::StateRecord;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::test_utils::create_test_signer;
use near_primitives::transaction::SignedTransaction;
use near_primitives::types::{AccountId, AccountInfo, Balance, Gas};
use near_primitives::version::PROTOCOL_VERSION;
use near_primitives_core::account::Account;
use near_store::test_utils::create_test_store;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct D3Params {
    pub base: ChainParams,
    pub max_txs: usize,
    /// D2: probability that an honest D2 transaction is a (D2 interpreter) contract call
    pub p_contract: f64,
    pub p_adv: f64,
    pub drop_cap: usize,
    /// per selected shard and height: number of D3 transactions is 0..=max_d3
    pub max_d3: usize,
    /// probability of code mutants for a D3 case outside the full-mutant sample
    pub code_mutant_p: f64,
    /// genesis `min_gas_price` (yoctoNEAR per gas; 0 = the TestEnv default, a zero gas price).
    /// A nonzero price exercises tokens_burnt, tx_burnt and the receiver reward.
    pub min_gas_price: u128,
}

const ACCTS_PER_SHARD: usize = 10;

fn acct(k: usize, j: usize) -> AccountId {
    format!("s{k}a{j:02}").parse().unwrap()
}

/// `chaind2::setup_d2` with the D3 contracts added to the genesis, and every contract of the
/// registry pre-compiled into every client's cache before the first block (the TestEnv
/// compilation / chunk-validation deadlock, see chaind2.rs).
pub fn setup_d3(p: &ChainParams, min_gas_price: u128) -> Setup {
    let accounts: Vec<Vec<AccountId>> = (0..p.n_shards).map(|k| (0..ACCTS_PER_SHARD).map(|j| acct(k, j)).collect()).collect();
    let boundaries: Vec<AccountId> = (1..p.n_shards).map(|k| format!("s{k}").parse().unwrap()).collect();
    let shard_layout = ShardLayout::multi_shard_custom(boundaries, 3);
    let validators = crate::chaind2::validators_of(p.n_shards);
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
    let genesis = Genesis::new(genesis_config, GenesisRecords(records)).unwrap();
    let mut clients = validators.clone();
    clients.extend(crate::chaind2::stakers_of());
    let n = clients.len();
    let stores: Vec<_> = (0..n).map(|_| create_test_store()).collect();
    let mut base: EpochConfig = (&genesis.config).into();
    base.block_producer_kickout_threshold = 0;
    base.chunk_producer_kickout_threshold = 0;
    let ecs = EpochConfigStore::test(BTreeMap::from_iter(vec![(genesis.config.protocol_version, Arc::new(base))]));
    let ems: Vec<Arc<EpochManagerHandle>> =
        stores.iter().map(|s| EpochManager::new_arc_handle_from_epoch_config_store(s.clone(), &genesis.config, ecs.clone())).collect();
    let clock = near_time::FakeClock::new(near_time::Utc::from_unix_timestamp(1_700_000_000).unwrap());
    let env = TestEnv::builder(&genesis.config)
        .clock(clock.clock())
        .clients(clients)
        .stores(stores)
        .epoch_managers(ems.clone())
        .save_tx_outcomes(true)
        .nightshade_runtimes_with_runtime_config_store(&genesis, vec![RuntimeConfigStore::new(None); n])
        .build();
    let wasm_config = RuntimeConfigStore::new(None).get_config(PROTOCOL_VERSION).wasm_config.clone();
    for c in &env.clients {
        let cache = c.runtime_adapter.compiled_contract_cache();
        for (_, code) in crate::d3contracts::all() {
            let code = near_vm_runner::ContractCode::new(code, None);
            near_vm_runner::precompile_contract(&code, Arc::clone(&wasm_config), Some(cache)).expect("cache").expect("compile");
        }
    }
    Setup { clock, env, ems, genesis, accounts }
}

/// Run one D3 chain; write cases under `out/{d3,ood,mutants}/<chain>-h<height>-s<shard>`.
pub fn run_chain_d3(chain_idx: usize, dp: &D3Params, out: &Path, o: &GenOpts, stats: &mut Stats, d3s: &mut crate::d3::D3Stats) {
    let p = &dp.base;
    let mut s = setup_d3(p, dp.min_gas_price);
    let cold_home = out.join(format!(".cold-{chain_idx}"));
    let judge = crate::d3judge::ColdJudge::new(&s.env.clients, &s.ems, &s.genesis, &cold_home);
    let mut world = crate::d2gen::World::new(&s.accounts, crate::chaind2::validators_of(p.n_shards), crate::chaind2::stakers_of());
    let mut w3 = crate::d3gen::D3World::new(p.n_shards);
    let mut labels: HashMap<CryptoHash, String> = HashMap::new();
    let mut rng = StdRng::seed_from_u64(p.seed);
    let mut ood_count: BTreeMap<String, usize> = BTreeMap::new();
    let mut d3_seen = 0usize;
    let mut pending_skips: HashMap<u64, Vec<AccountId>> = HashMap::new();
    let reg = crate::d3contracts::registry();
    let tip0 = s.env.clients[0].chain.head().unwrap();
    let mut height = tip0.height;
    for round in 0..p.blocks {
        height += 1;
        if std::env::var("D3_TRACE").is_ok() {
            eprintln!("round {round} height {height}");
        }
        s.clock.advance(near_time::Duration::milliseconds(1100));
        let tip = s.env.clients[0].chain.head().unwrap();
        {
            let em = s.ems[0].read();
            world.minimum_stake = em.minimum_stake(&tip.last_block_hash).map(|b| b.as_yoctonear()).unwrap_or(0);
        }
        // ---- honest transactions: D2 traffic + D3 traffic
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
                world.yield_bias = false;
                txs.extend(world.gen_txs(&s, &tip.last_block_hash, height, &mut rng, n, dp.p_contract));
                let m = rng.gen_range(0..=dp.max_d3);
                for _ in 0..m {
                    if let Some(x) = w3.one(&mut world, &s, &tip.last_block_hash, height, &mut rng) {
                        txs.push(x);
                    }
                }
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
        // ---- block
        let bp = s.env.get_block_producer_at_offset(&tip, height - tip.height);
        if !s.env.contains_client(&bp) {
            panic!("block producer {bp} at height {height} has no client");
        }
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
                let Some(crafted) = craft(&s, k, &block, height, p, &mut rng) else {
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
                crate::d1gen::produce_chunks_with_injection(&mut s.env.clients[i], &block, Some((sid, crafted.into_iter().map(|x| x.1).collect())), &mut rng);
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

        // ---- judge (cold validator, needed codes appended), classify, write
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
            // the needed codes: nearcore's contract accesses of the main transition, in the
            // order of their hashes (the bytes from the code registry)
            let mut codes: Vec<Vec<u8>> = Vec::new();
            let mut missing = false;
            for h in &accesses {
                match reg.by_hash.get(h) {
                    Some((_, c)) => codes.push(c.clone()),
                    None => missing = true,
                }
            }
            if missing {
                eprintln!("WARNING: a contract access outside the code registry");
                d3s.add("check.access_not_in_registry", 1);
            }
            let wb = borsh::to_vec(&sw).unwrap();
            let rs = (built.claim.rs_data_parts, built.claim.rs_total_parts);
            let verdict = judge.judge(ci, client, &wb, &codes, rs, None);
            if verdict.is_ok() {
                stats.honest_ok += 1;
            } else {
                eprintln!("honest witness rejected by the cold validator: {:?}", verdict);
            }
            // the TestEnv's own (warm-cache) verdict without codes, and the cold one without codes
            let warm = crate::judge::nearcore_judge(client, &wb, &[], rs);
            if warm.is_ok() {
                d3s.add("honest_warm_no_codes_ok", 1);
            }
            let cold_nc = if codes.is_empty() { None } else { Some(judge.judge(ci, client, &wb, &[], rs, None)) };
            if let Some(r) = &cold_nc {
                d3s.add(if r.is_ok() { "honest_cold_no_codes_ok" } else { "honest_cold_no_codes_reject" }, 1);
            }
            let tracker = (0..s.env.clients.len()).map(|k| &s.env.clients[k]).find(|c| crate::d0::tracks(c, &built)).unwrap_or(client);
            crate::d3::write_d3_case(
                crate::d3::D3Ctx {
                    tracker,
                    client,
                    ci,
                    judge: &judge,
                    built: &built,
                    sw: &sw,
                    wb: &wb,
                    accesses: &accesses,
                    codes: &codes,
                    verdict: &verdict,
                    warm: &warm,
                    cold_no_codes: cold_nc.as_ref(),
                    labels: &labels,
                    chain_idx,
                    params: &format!("{dp:?}"),
                    n_shards: p.n_shards,
                    out,
                    o,
                    rng: &mut rng,
                    ood_count: &mut ood_count,
                    d3_seen: &mut d3_seen,
                    drop_cap: dp.drop_cap,
                    code_mutant_p: dp.code_mutant_p,
                },
                stats,
                d3s,
            );
        }
    }
    let _ = std::fs::remove_dir_all(&cold_home);
}

/// D2 crafted transactions for shard index `k` (oracle/v3-d1/src/chaind2.rs `craft_for_d2`,
/// private there).
fn craft(s: &Setup, k: usize, block: &near_chain::Block, height: u64, p: &ChainParams, rng: &mut StdRng) -> Option<Vec<(String, SignedTransaction)>> {
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
