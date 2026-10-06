//! Chain generation with nearcore's own TestEnv (real NightshadeRuntime, epoch
//! manager, block and chunk production, real witness production), witness
//! capture, claim building, nearcore judging, D0 classification, mutants.

use crate::claim::{block_rec, build_claim};
use crate::enc::{Claim, encode_witness};
use crate::judge::nearcore_judge;
use crate::a2mut::foreign_routing;
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
    pub honest: usize,
    pub honest_ok: usize,
    pub d0: usize,
    pub ood_written: usize,
    pub mutants: usize,
    pub by_violation: BTreeMap<String, usize>,
    /// Arena layout: honest positives written to `cases/` (class-matching D0 cases).
    pub positives: usize,
    /// Arena layout: cases written to `rejections/` (expected_rel_d0 = false).
    pub rejections: usize,
}

/// Workload class of an honest D0 case (spec/workloads/near-chunk-validation-d0/*.json):
/// `quiet` = no incoming receipt and no implicit transition, `transfers` = at least one
/// incoming receipt and no implicit transition, `missing` = at least one implicit
/// transition (missing chunks of the shard before the endorsed chunk); `any` = all.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaseClass {
    Any,
    Quiet,
    Transfers,
    Missing,
}

impl CaseClass {
    pub fn parse(s: &str) -> Option<Self> {
        Some(match s {
            "any" => CaseClass::Any,
            "quiet" => CaseClass::Quiet,
            "transfers" => CaseClass::Transfers,
            "missing" => CaseClass::Missing,
            _ => return None,
        })
    }
    pub fn matches(self, n_receipts: usize, n_implicit: usize) -> bool {
        match self {
            CaseClass::Any => true,
            CaseClass::Quiet => n_receipts == 0 && n_implicit == 0,
            CaseClass::Transfers => n_receipts > 0 && n_implicit == 0,
            CaseClass::Missing => n_implicit > 0,
        }
    }
}

/// Output options of `gen`.
#[derive(Clone, Debug)]
pub struct GenOpts {
    pub ood_cap: usize,
    pub mutate_every: usize,
    /// Arena fixtures layout (runners/worker `NearV3Oracle`, `arena check-local`):
    /// `cases/<n>/{request.bin, witness.bin, expected_claim.bin, meta.json}` for cases with
    /// `expected_rel_d0 = true` (request = expected claim = claim.bin: the claim is the job),
    /// `rejections/<n>/{request.bin, witness.bin, meta.json}` for `expected_rel_d0 = false`
    /// (nearcore rejects, or the honest chunk is outside D0). Otherwise `d0/`, `ood/`,
    /// `mutants/` with `claim.bin`, `witness.bin`, `meta.json` (difftest layout).
    pub fixtures_layout: bool,
    /// Honest D0 cases written as positives (others are skipped, still mutated).
    pub class: CaseClass,
    /// Write no positives at all (rejection sampling).
    pub no_positives: bool,
    /// Arena layout: also write nearcore-accepted D0 mutants as positives.
    pub accepted_mutants: bool,
    /// Stop once this many honest positives were written (0 = no target).
    pub positive_target: usize,
    /// Stop once this many rejections were written (0 = no target).
    pub rejection_target: usize,
    /// At most this many honest positives per chain (0 = no cap), so a batch
    /// spans several chain parameter sets (shard counts, Reed-Solomon codes).
    pub per_chain_cap: usize,
}

impl GenOpts {
    /// Every non-zero target reached (and at least one target set).
    pub fn done(&self, st: &Stats) -> bool {
        let p = self.positive_target == 0 || st.positives >= self.positive_target;
        let r = self.rejection_target == 0 || st.rejections >= self.rejection_target;
        (self.positive_target > 0 || self.rejection_target > 0) && p && r
    }
}

fn write_case(dir: &Path, claim: &Claim, witness: &[u8], meta: serde_json::Value) {
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("claim.bin"), claim.encode()).unwrap();
    std::fs::write(dir.join("witness.bin"), encode_witness(witness, &[])).unwrap();
    std::fs::write(dir.join("meta.json"), serde_json::to_string_pretty(&meta).unwrap()).unwrap();
}

/// Arena layout: a positive (`expected_rel_d0`) case or a rejection.
fn write_arena_case(out: &Path, name: &str, positive: bool, claim: &Claim, witness: &[u8], meta: serde_json::Value) {
    let dir = out.join(if positive { "cases" } else { "rejections" }).join(name);
    std::fs::create_dir_all(&dir).unwrap();
    let c = claim.encode();
    std::fs::write(dir.join("request.bin"), &c).unwrap();
    if positive {
        std::fs::write(dir.join("expected_claim.bin"), &c).unwrap();
    }
    std::fs::write(dir.join("witness.bin"), encode_witness(witness, &[])).unwrap();
    std::fs::write(dir.join("meta.json"), serde_json::to_string_pretty(&meta).unwrap()).unwrap();
}

/// Run one chain; write cases under `out/<chain>-...`.
pub fn run_chain(chain_idx: usize, p: &ChainParams, out: &Path, o: &GenOpts, stats: &mut Stats) {
    let (ood_cap, mutate_every) = (o.ood_cap, o.mutate_every);
    let mut s = setup(p);
    let mut rng = StdRng::seed_from_u64(p.seed);
    let mut nonces: HashMap<AccountId, u64> = HashMap::new();
    let mut fail_ctr = 0u64;
    let mut ood_count: BTreeMap<String, usize> = BTreeMap::new();
    let mut d0_seen = 0usize;
    let mut pending_skips: HashMap<u64, Vec<AccountId>> = HashMap::new();
    let tip0 = s.env.clients[0].chain.head().unwrap();
    let mut height = tip0.height;
    let rs = (
        s.env.clients[0].epoch_manager.num_data_parts() as u16,
        s.env.clients[0].epoch_manager.num_total_parts() as u16,
    );
    let mut chain_pos = 0usize;
    for _round in 0..p.blocks {
        if o.done(stats) {
            break;
        }
        if o.per_chain_cap > 0 && chain_pos >= o.per_chain_cap && o.rejection_target == 0 {
            break;
        }
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
            for _ in 0..n {
                let signer_id = s.accounts[k][rng.gen_range(0..ACCTS_PER_SHARD)].clone();
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
                    (s.accounts[ts][rng.gen_range(0..ACCTS_PER_SHARD)].clone(), 2)
                } else {
                    (s.accounts[ts][rng.gen_range(0..ACCTS_PER_SHARD)].clone(), 1)
                };
                let deposit = Balance::from_yoctonear(rng.gen_range(1..10u128.pow(24)));
                let acts = (0..actions).map(|_| Action::Transfer(TransferAction { deposit })).collect();
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
        // ---- block
        let bp = s.env.get_block_producer_at_offset(&tip, height - tip.height);
        let block = s.env.client(&bp).produce_block(height).unwrap().unwrap();
        for i in 0..s.env.clients.len() {
            let skip = force_skip.contains(&s.env.get_client_id(i)) || rng.gen_bool(p.p_missing);
            let r = if skip {
                s.env.clients[i].process_block_test_no_produce_chunk(block.clone().into(), Provenance::NONE)
            } else {
                s.env.clients[i].process_block_test(block.clone().into(), Provenance::NONE)
            };
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
            // D0a = D0 ∧ amendments (A1, A2, Canon0f)
            let in_d0_orig = viol.is_empty();
            let mut viol = viol;
            match crate::d0a::extra(tracker, &built, &sw) {
                Ok(x) => viol.extend(x),
                Err(e) => {
                    eprintln!("d0a classify failed: {e}");
                    continue;
                }
            }
            // A7: unfolded trie bytes (only meaningful when nearcore accepted the witness)
            let unfold = if verdict.is_ok() {
                match crate::d0a::unfold_bytes(tracker, &built, &sw) {
                    Ok(u) => u,
                    Err(e) => {
                        eprintln!("unfold failed: {e}");
                        None
                    }
                }
            } else {
                None
            };
            if unfold.map_or(false, |u| u > crate::d0a::B0) {
                viol.push("w.unfolded");
            }
            let in_d0 = viol.is_empty();
            let key = sw.chunk_production_key();
            let name = format!("{chain_idx:02}-h{}-s{}", key.height_created, key.shard_id);
            for v in &viol {
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
                "domain": "D0a",
                "in_d0": in_d0_orig, "expected_rel_d0": verdict.is_ok() && in_d0_orig,
                "in_d0a": in_d0, "d0a_violations": viol,
                "expected_rel_d0a": verdict.is_ok() && in_d0,
                "unfold_bytes": unfold,
                "features": features,
            });
            let n_receipts = match &sw { ChunkStateWitness::V2(x) => x.source_receipt_proofs.values().map(|p| p.0.len()).sum::<usize>() };
            if in_d0 {
                stats.d0 += 1;
                if o.fixtures_layout {
                    let pos = verdict.is_ok();
                    if !pos {
                        if o.rejection_target == 0 || stats.rejections < o.rejection_target {
                            stats.rejections += 1;
                            write_arena_case(out, &name, false, &built.claim, &wb, meta);
                        }
                    } else if !o.no_positives
                        && o.class.matches(n_receipts, built.implicit.len())
                        && (o.positive_target == 0 || stats.positives < o.positive_target)
                        && (o.per_chain_cap == 0 || chain_pos < o.per_chain_cap)
                    {
                        stats.positives += 1;
                        chain_pos += 1;
                        write_arena_case(out, &name, true, &built.claim, &wb, meta);
                    }
                } else {
                    write_case(&out.join("d0").join(&name), &built.claim, &wb, meta);
                }
                d0_seen += 1;
                // A2 mutant on every accepted D0a case whose segment starts at B2 (no RNG use)
                if verdict.is_ok() && built.b2 == 0 && !o.fixtures_layout {
                    let em = client.epoch_manager.as_ref();
                    if let Ok(layout) = em.get_shard_layout(built.blocks[0].header().epoch_id()) {
                        if let Some(m) = foreign_routing(&built.claim, &sw, &layout, built.shard_id) {
                            let mname = format!("{name}-{}", m.name);
                            let meta = json!({
                                "case": mname, "kind": "mutant", "mutation": m.name, "base": name,
                                "domain": "D0a", "verdict_source": "construction",
                                "nearcore": "not judged (mutated block not in the store); Rel holds by construction",
                                "expected_rel": true,
                                "in_d0": true, "expected_rel_d0": true,
                                "in_d0a": false, "d0a_violations": ["w.proof_routing"],
                                "expected_rel_d0a": false,
                                "expected_verdict": "out_of_domain",
                            });
                            stats.mutants += 1;
                            write_case(&out.join("mutants").join(&mname), &m.claim, &m.witness, meta);
                        }
                    }
                }
                if verdict.is_ok() && mutate_every > 0 && d0_seen % mutate_every == 0 {
                    let last = built.blocks.last().unwrap();
                    let parent = if last.header().is_genesis() {
                        None
                    } else {
                        client.chain.get_block(last.header().prev_hash()).ok().and_then(|b| block_rec(&b).ok())
                    };
                    let mut ms = mutants(&built.claim, &sw, parent, &mut rng);
                    if d0_seen % (mutate_every * 2) == 0 {
                        ms.extend(drop_each_node(&built.claim, &sw, 48));
                    }
                    for m in ms {
                        let (exp, src) = match m.judge {
                            Judge::Claim => (Err("claim-v3 discipline".to_string()), "claim-v3"),
                            Judge::Nearcore => (
                                nearcore_judge(client, &m.witness, &[], (m.claim.rs_data_parts, m.claim.rs_total_parts)),
                                "nearcore",
                            ),
                        };
                        let mname = format!("{name}-{}", m.name);
                        let meta = json!({
                            "case": mname, "kind": "mutant", "mutation": m.name, "base": name,
                            "verdict_source": src,
                            "nearcore": exp.as_ref().map(|_| "ok".to_string()).unwrap_or_else(|e| e.clone()),
                            "expected_rel": exp.is_ok(),
                            "domain": "D0a",
                            "in_d0": true, "expected_rel_d0": exp.is_ok(),
                            "in_d0a": true, "d0a_violations": [],
                            "expected_rel_d0a": exp.is_ok(),
                        });
                        stats.mutants += 1;
                        if o.fixtures_layout {
                            let pos = exp.is_ok();
                            // A mutant whose claim header (protocol version, chain id) differs
                            // from the chain's is a true claim about another chain: never issued
                            // by the judge (the arena's request pin refuses it), so not written.
                            let same_header = m.claim.protocol_version == built.claim.protocol_version
                                && m.claim.chain_id == built.claim.chain_id;
                            if !same_header {
                            } else if pos && o.accepted_mutants && !o.no_positives {
                                write_arena_case(out, &mname, true, &m.claim, &m.witness, meta);
                            } else if !pos && (o.rejection_target == 0 || stats.rejections < o.rejection_target) {
                                stats.rejections += 1;
                                write_arena_case(out, &mname, false, &m.claim, &m.witness, meta);
                            }
                        } else {
                            write_case(&out.join("mutants").join(&mname), &m.claim, &m.witness, meta);
                        }
                    }
                }
            } else {
                let fam = viol.join("+");
                let c = ood_count.entry(fam).or_default();
                if *c < ood_cap && !(o.fixtures_layout && o.rejection_target > 0 && stats.rejections >= o.rejection_target) {
                    *c += 1;
                    stats.ood_written += 1;
                    if o.fixtures_layout {
                        stats.rejections += 1;
                        write_arena_case(out, &name, false, &built.claim, &wb, meta);
                    } else {
                        write_case(&out.join("ood").join(&name), &built.claim, &wb, meta);
                    }
                }
            }
        }
    }
    let _ = rs;
}
