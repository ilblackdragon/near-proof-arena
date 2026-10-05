//! Leaf-primitive test vectors produced by nearcore's own code, for the Lean
//! leaf modules (spec/lean/NearSpec/V3/*) and the Python checker:
//!   chacha.json      ChaCha20Rng (rand_chacha 0.3.1) u32 stream + nearcore's
//!                    `shuffle_receipt_proofs` permutations
//!   congestion.json  `CongestionControl::congestion_level` (f64 bits),
//!                    `is_fully_congested`, `outgoing_gas_limit`
//!   rs.json          `reed_solomon_encode` + `EncodedShardChunkBody` merkle root
//!   scheduler.json   the bandwidth-scheduler state write of a real
//!                    `Runtime::apply` for a missing chunk (is_new_chunk = false)

use near_parameters::RuntimeConfigStore;
use near_primitives::apply::ApplyChunkReason;
use near_primitives::bandwidth_scheduler::{
    BandwidthRequest, BandwidthRequestBitmap, BandwidthRequests, BandwidthRequestsV1,
    BandwidthSchedulerState, BandwidthSchedulerStateV1, BlockBandwidthRequests, LinkAllowance,
};
use near_primitives::congestion_info::{
    BlockCongestionInfo, CongestionControl, CongestionInfo, CongestionInfoV1, ExtendedCongestionInfo,
};
use near_primitives::hash::CryptoHash;
use near_primitives::sharding::EncodedShardChunkBody;
use near_primitives::shard_layout::ShardLayout;
use near_primitives::test_utils::MockEpochInfoProvider;
use near_primitives::trie_key::TrieKey;
use near_primitives::types::{AccountId, Balance, EpochId, Gas, ShardId};
use near_store::ShardTries;
use near_store::test_utils::TestTriesBuilder;
use near_store::trie::AccessOptions;
use node_runtime::{ApplyState, Runtime, SignedValidPeriodTransactions};
use rand::rngs::StdRng;
use rand::{Rng, RngCore, SeedableRng};
use reed_solomon_erasure::galois_8::ReedSolomon;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::Path;

fn hx(b: &[u8]) -> String {
    hex::encode(b)
}

fn chacha(rng: &mut StdRng) -> Value {
    use rand_chacha::ChaCha20Rng;
    let mut streams = Vec::new();
    for _ in 0..12 {
        let seed: [u8; 32] = rng.r#gen();
        let mut c = ChaCha20Rng::from_seed(seed);
        let words: Vec<u32> = (0..80).map(|_| c.next_u32()).collect();
        streams.push(json!({"seed": hx(&seed), "u32": words}));
    }
    let mut shuffles = Vec::new();
    for i in 0..400 {
        let seed: [u8; 32] = if i < 3 { [i as u8; 32] } else { rng.r#gen() };
        let n = if i < 40 { i % 20 } else { rng.gen_range(0..64) };
        let mut v: Vec<u32> = (0..n as u32).collect();
        near_chain::sharding::shuffle_receipt_proofs(&mut v, &CryptoHash(seed));
        shuffles.push(json!({"seed": hx(&seed), "n": n, "perm": v}));
    }
    // nearcore's own test vector (sharding.rs:29-33)
    let mut v: Vec<u32> = (0..7).collect();
    near_chain::sharding::shuffle_receipt_proofs(&mut v, &near_primitives::hash::hash(&[1, 2, 3, 4, 5]));
    json!({"streams": streams, "shuffles": shuffles, "nearcore_test_vector": v})
}

fn pick_u128(rng: &mut StdRng, max: u128) -> u128 {
    match rng.gen_range(0..24) {
        0 => 0,
        1 => max,
        2 => max - rng.gen_range(0..=64u128).min(max),
        3 => max + rng.gen_range(0..=64u128),
        4 => max.saturating_sub(rng.gen_range(0..1_000_000u128)),
        5 => rng.r#gen::<u128>(),
        _ => rng.gen_range(0..max),
    }
}

fn congestion(rng: &mut StdRng) -> Value {
    let cfg = RuntimeConfigStore::new(None).get_config(86).congestion_control_config;
    let mut out = Vec::new();
    for _ in 0..3000 {
        let delayed = pick_u128(rng, cfg.max_congestion_incoming_gas.as_gas() as u128);
        let buffered = pick_u128(rng, cfg.max_congestion_outgoing_gas.as_gas() as u128);
        let bytes = pick_u128(rng, cfg.max_congestion_memory_consumption as u128) as u64;
        let allowed: u16 = rng.gen_range(0..8);
        let missed: u64 = match rng.gen_range(0..8) {
            0 | 1 | 2 | 3 => 0,
            4 => rng.gen_range(1..4),
            5 => rng.gen_range(120..130),
            _ => rng.gen_range(0..125),
        };
        let info = CongestionInfo::V1(CongestionInfoV1 {
            delayed_receipts_gas: delayed,
            buffered_receipts_gas: buffered,
            receipt_bytes: bytes,
            allowed_shard: allowed,
        });
        let cc = CongestionControl::new(cfg, info, missed);
        let level = cc.congestion_level();
        out.push(json!({
            "delayed_receipts_gas": delayed.to_string(), "buffered_receipts_gas": buffered.to_string(),
            "receipt_bytes": bytes, "allowed_shard": allowed, "missed_chunks_count": missed,
            "level_bits": format!("{:016x}", level.to_bits()),
            "fully_congested": CongestionControl::is_fully_congested(level),
            "outgoing_gas_limit_from_allowed": cc.outgoing_gas_limit(ShardId::new(allowed as u64)).as_gas(),
            "outgoing_gas_limit_from_other": cc.outgoing_gas_limit(ShardId::new(allowed as u64 + 1)).as_gas(),
        }));
    }
    json!({"config": {
        "max_congestion_incoming_gas": cfg.max_congestion_incoming_gas.as_gas(),
        "max_congestion_outgoing_gas": cfg.max_congestion_outgoing_gas.as_gas(),
        "max_congestion_memory_consumption": cfg.max_congestion_memory_consumption,
        "max_congestion_missed_chunks": cfg.max_congestion_missed_chunks,
        "max_outgoing_gas": cfg.max_outgoing_gas.as_gas(), "min_outgoing_gas": cfg.min_outgoing_gas.as_gas(),
        "allowed_shard_outgoing_gas": cfg.allowed_shard_outgoing_gas.as_gas()}, "cases": out})
}

fn rs(rng: &mut StdRng) -> Value {
    let mut out = Vec::new();
    for &(d, total) in &[(1usize, 2usize), (1, 3), (2, 8), (5, 16), (33, 100), (1, 4), (3, 10), (85, 256)] {
        let r = ReedSolomon::new(d, total - d).unwrap();
        for &len in &[0usize, 1, 2, 7, 33, 100, 255, 1000, 4321] {
            let payload: Vec<u8> = (0..len).map(|_| rng.r#gen()).collect();
            let (parts, enc_len) = near_primitives::reed_solomon::reed_solomon_encode(&r, &payload);
            let body = EncodedShardChunkBody { parts };
            let (root, _) = body.get_merkle_hash_and_paths();
            let part_hashes: Vec<String> = body
                .parts
                .iter()
                .map(|p| hx(&near_primitives::hash::hash(p.as_deref().unwrap()).0))
                .collect();
            out.push(json!({"data_parts": d, "total_parts": total,
                "borsh_bytes": hx(&borsh::to_vec(&payload).unwrap()),
                "encoded_length": enc_len, "encoded_merkle_root": hx(&root.0),
                "part_sha256": part_hashes}));
        }
    }
    json!({"cases": out})
}

fn scheduler(rng: &mut StdRng) -> Value {
    let config = RuntimeConfigStore::new(None).get_config(86).clone();
    let mut out = Vec::new();
    for case in 0..600 {
        let n: usize = [1usize, 2, 3, 4, 5, 6, 8, 9][case % 8];
        let boundaries: Vec<AccountId> = (1..n).map(|k| format!("b{k}").parse().unwrap()).collect();
        let layout = ShardLayout::multi_shard_custom(boundaries, 3);
        let ids: Vec<ShardId> = layout.shard_ids().collect();
        let own = ids[rng.gen_range(0..n)];
        let provider = MockEpochInfoProvider::new(layout.clone());
        // previous state: absent, or random allowances (incl. stale shard ids)
        let prev: Option<BandwidthSchedulerState> = if rng.gen_bool(0.2) {
            None
        } else {
            let mut la = Vec::new();
            for &s in &ids {
                for &r in &ids {
                    if rng.gen_bool(0.85) {
                        let allowance = match rng.gen_range(0..4) {
                            0 => 0,
                            1 => 4_500_000,
                            2 => rng.gen_range(0..200_000),
                            _ => rng.gen_range(0..4_500_001),
                        };
                        la.push(LinkAllowance { sender: s, receiver: r, allowance });
                    }
                }
            }
            if rng.gen_bool(0.2) {
                la.push(LinkAllowance { sender: ShardId::new(77), receiver: ids[0], allowance: 5 });
            }
            Some(BandwidthSchedulerState::V1(BandwidthSchedulerStateV1 {
                link_allowances: la,
                sanity_check_hash: CryptoHash(rng.r#gen()),
            }))
        };
        // block congestion info / missed chunks for (a subset of) shards
        let mut ci = BTreeMap::new();
        let cfg = config.congestion_control_config;
        for &s in &ids {
            if rng.gen_bool(0.95) {
                let fully = rng.gen_bool(0.2);
                let info = CongestionInfo::V1(CongestionInfoV1 {
                    delayed_receipts_gas: if fully && rng.gen_bool(0.5) {
                        cfg.max_congestion_incoming_gas.as_gas() as u128 - rng.gen_range(0..40u128)
                    } else {
                        rng.gen_range(0..1_000_000_000_000_000u128)
                    },
                    buffered_receipts_gas: if fully && rng.gen_bool(0.5) {
                        cfg.max_congestion_outgoing_gas.as_gas() as u128
                    } else {
                        rng.gen_range(0..1_000_000_000u128)
                    },
                    receipt_bytes: rng.gen_range(0..1000),
                    allowed_shard: u64::from_le_bytes(ids[rng.gen_range(0..n)].to_le_bytes()) as u16,
                });
                let missed = match rng.gen_range(0..5) {
                    0 => 1,
                    1 => rng.gen_range(2..200),
                    _ => 0,
                };
                ci.insert(s, ExtendedCongestionInfo::new(info, missed));
            }
        }
        // bandwidth requests
        let mut reqs = BTreeMap::new();
        for &s in &ids {
            if rng.gen_bool(0.6) {
                let mut v = Vec::new();
                for &r in &ids {
                    if rng.gen_bool(0.5) {
                        let mut bm = BandwidthRequestBitmap::new();
                        for b in 0..40 {
                            if rng.gen_bool(0.15) {
                                bm.set_bit(b, true);
                            }
                        }
                        v.push(BandwidthRequest { to_shard: u64::from_le_bytes(r.to_le_bytes()) as u16, requested_values_bitmap: bm });
                    }
                }
                if rng.gen_bool(0.1) {
                    let mut bm = BandwidthRequestBitmap::new();
                    bm.set_bit(39, true);
                    v.push(BandwidthRequest { to_shard: 99, requested_values_bitmap: bm });
                }
                reqs.insert(s, BandwidthRequests::V1(BandwidthRequestsV1 { requests: v }));
            }
        }
        let prev_hash = CryptoHash(rng.r#gen());
        let height: u64 = rng.gen_range(1..u64::MAX / 2);

        let tries: ShardTries = TestTriesBuilder::new().build();
        let shard_uid = near_primitives::shard_layout::ShardUId::from_shard_id_and_layout(own, &layout);
        let empty = tries.get_trie_for_shard(shard_uid, CryptoHash::default());
        let key = TrieKey::BandwidthSchedulerState.to_vec();
        let prev_bytes = prev.as_ref().map(|p| borsh::to_vec(p).unwrap());
        // a few unrelated keys so the 0x0f write exercises trie shapes
        let mut changes: Vec<(Vec<u8>, Option<Vec<u8>>)> = vec![(vec![0x00, b'a', b'b'], Some(vec![1; 72]))];
        if let Some(b) = &prev_bytes {
            changes.push((key.clone(), Some(b.clone())));
        }
        let tc = empty.update(changes, AccessOptions::DEFAULT).unwrap();
        let mut su = tries.store_update();
        let pre_root = tries.apply_all(&tc, shard_uid, &mut su);
        su.commit();
        let apply_state = ApplyState {
            apply_reason: ApplyChunkReason::UpdateTrackedShard,
            block_height: height,
            prev_block_hash: prev_hash,
            shard_id: own,
            epoch_id: EpochId::default(),
            epoch_height: 0,
            gas_price: Balance::from_yoctonear(100_000_000),
            block_timestamp: 1_000,
            gas_limit: Some(Gas::from_teragas(1000)),
            random_seed: CryptoHash::default(),
            current_protocol_version: 86,
            config: std::sync::Arc::new(config.as_ref().clone()),
            next_wasm_config: None,
            cache: None,
            trie_access_tracker_state: Default::default(),
            is_new_chunk: false,
            save_receipt_to_tx: false,
            congestion_info: BlockCongestionInfo::new(ci.clone()),
            bandwidth_requests: BlockBandwidthRequests { shards_bandwidth_requests: reqs.clone() },
            on_post_state_ready: None,
        };
        let trie = tries.get_trie_for_shard(shard_uid, pre_root);
        let res = Runtime::new()
            .apply(trie, &None, &apply_state, &[], SignedValidPeriodTransactions::empty(), &provider, Default::default())
            .unwrap();
        let post = res
            .state_changes
            .iter()
            .find(|c| c.trie_key == TrieKey::BandwidthSchedulerState)
            .and_then(|c| c.changes.last())
            .and_then(|c| c.data.clone())
            .expect("scheduler state written");
        let cis: Vec<Value> = ci
            .iter()
            .map(|(s, e)| {
                let i = e.congestion_info;
                json!({"shard_id": u64::from_le_bytes(s.to_le_bytes()),
                    "delayed_receipts_gas": i.delayed_receipts_gas().to_string(),
                    "buffered_receipts_gas": i.buffered_receipts_gas().to_string(),
                    "receipt_bytes": i.receipt_bytes(), "allowed_shard": i.allowed_shard(),
                    "missed_chunks_count": e.missed_chunks_count})
            })
            .collect();
        let rq: Vec<Value> = reqs
            .iter()
            .map(|(s, r)| json!({"shard_id": u64::from_le_bytes(s.to_le_bytes()), "requests_borsh": hx(&borsh::to_vec(r).unwrap())}))
            .collect();
        out.push(json!({
            "shard_layout_borsh": hx(&borsh::to_vec(&layout).unwrap()),
            "own_shard_id": u64::from_le_bytes(own.to_le_bytes()),
            "prev_block_hash": hx(&prev_hash.0), "block_height": height,
            "prev_state_borsh": prev_bytes.map(|b| hx(&b)),
            "congestion": cis, "bandwidth_requests": rq,
            "post_state_borsh": hx(&post),
            "pre_root": hx(&pre_root.0), "post_root": hx(&res.state_root.0),
        }));
    }
    json!({"cases": out})
}

pub fn cmd_vectors(out: &Path, seed: u64) -> i32 {
    std::fs::create_dir_all(out).unwrap();
    let mut rng = StdRng::seed_from_u64(seed);
    let w = |name: &str, v: Value| std::fs::write(out.join(name), serde_json::to_string(&v).unwrap()).unwrap();
    w("chacha.json", chacha(&mut rng));
    w("congestion.json", congestion(&mut rng));
    w("rs.json", rs(&mut rng));
    w("scheduler.json", scheduler(&mut rng));
    0
}
