//! Opt-in (`NEAR_SUCCESSOR_OBSERVABLES=1`): nearcore's own per-outcome observables for every honest
//! witness the generator captures (workplan W01). Off, nothing here runs and the generator's output
//! is unchanged; on, it only *adds* `nearcore-observables-<chain>.jsonl` to the output directory and
//! never touches the generator's RNG, so the cases it writes are byte-identical.
//!
//! For each witness it runs the main state transition the way the stateless validator does
//! (`validate_chunk_state_witness_impl`, `chunk_validation.rs:600-616`): a *cold* validator runtime
//! (empty compiled-contract cache, its own `NightshadeRuntime` over the client's store) pre-validates
//! the witness with the needed code blobs appended and calls `apply_new_chunk` with
//! `ApplyChunkReason::ValidateChunkStateWitness`. The `ApplyChunkResult` gives the execution
//! outcomes, outgoing receipts and committed state changes (`WrappedTrieChanges::state_changes`,
//! the `TrieUpdate` committed overlay at `finalize`, rollbacks applied). The producer's stored
//! outcome ids (`get_outcomes_by_block_hash_and_shard_id`) are recorded too, as a cross-check.
//!
//! Each record is keyed by the sha256 of the case's `claim.bin` and `witness.bin` bytes, so a
//! comparator can bind it to a case directory without trusting names.

use crate::d3judge::ColdCache;
use crate::enc::encode_witness;
use near_chain::ChainStoreAccess;
use near_chain::chain::{ShardContext, apply_new_chunk};
use near_chain::runtime::NightshadeRuntime;
use near_chain::stateless_validation::chunk_validation::{MainTransition, pre_validate_chunk_state_witness};
use near_chain::types::{ApplyChunkResult, MaybePinnedMemtrieRoot};
use near_client::Client;
use near_epoch_manager::shard_assignment::shard_id_to_uid;
use near_epoch_manager::{EpochManagerAdapter, EpochManagerHandle};
use near_primitives::apply::ApplyChunkReason;
use near_primitives::hash::CryptoHash;
use near_primitives::transaction::ExecutionStatus;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::io::Write;
use std::path::Path;
use std::sync::Arc;

pub fn enabled() -> bool {
    std::env::var("NEAR_SUCCESSOR_OBSERVABLES").is_ok_and(|v| !v.is_empty() && v != "0")
}

fn sha(b: &[u8]) -> String {
    hex::encode(Sha256::digest(b))
}

fn h(x: &CryptoHash) -> String {
    hex::encode(x.0)
}

pub struct Collector {
    rts: Vec<(Arc<NightshadeRuntime>, ColdCache)>,
    file: std::io::BufWriter<std::fs::File>,
}

impl Collector {
    pub fn new(clients: &[Client], ems: &[Arc<EpochManagerHandle>], genesis: &near_chain_configs::Genesis, home: &Path, out: &Path, chain_idx: usize) -> Self {
        let rts = clients
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let cache = ColdCache::default();
                let dir = home.join(format!("obs-{i}"));
                std::fs::create_dir_all(&dir).unwrap();
                let rt = NightshadeRuntime::test_with_runtime_config_store(
                    &dir,
                    c.chain.chain_store().store(),
                    Box::new(cache.clone()),
                    &genesis.config,
                    ems[i].clone(),
                    near_parameters::RuntimeConfigStore::new(None),
                );
                (rt, cache)
            })
            .collect();
        let path = out.join(format!("nearcore-observables-{chain_idx:02}.jsonl"));
        let file = std::io::BufWriter::new(std::fs::File::create(path).unwrap());
        Collector { rts, file }
    }

    /// Record one honest witness (`wb` = borsh `ChunkStateWitness`, `codes` = the appended blobs).
    pub fn record(&mut self, ci: usize, client: &Client, wb: &[u8], codes: &[Vec<u8>], claim_bytes: &[u8], chain_idx: usize) {
        let (rt, cache) = &self.rts[ci];
        cache.clear();
        let body = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| observe(client, rt.as_ref(), wb, codes))) {
            Ok(Ok(v)) => v,
            Ok(Err(e)) => json!({ "status": format!("error: {e}") }),
            Err(_) => json!({ "status": "error: panic" }),
        };
        cache.clear();
        let mut rec = json!({
            "chain": chain_idx,
            "claim_sha256": sha(claim_bytes),
            "witness_sha256": sha(&encode_witness(wb, codes)),
        });
        if let (Value::Object(m), Value::Object(b)) = (&mut rec, body) {
            m.extend(b);
        }
        writeln!(self.file, "{}", serde_json::to_string(&rec).unwrap()).unwrap();
        self.file.flush().unwrap();
    }
}

pub fn status_json(s: &ExecutionStatus) -> Value {
    match s {
        ExecutionStatus::SuccessValue(v) => json!({ "kind": "value", "value": hex::encode(v) }),
        ExecutionStatus::SuccessReceiptId(r) => json!({ "kind": "receipt", "receiptId": h(r) }),
        ExecutionStatus::Failure(e) => json!({ "kind": "failure", "error": format!("{e:?}") }),
        ExecutionStatus::Unknown => json!({ "kind": "unknown" }),
    }
}

fn receipt_kind(r: &near_primitives::receipt::Receipt) -> String {
    let d = format!("{:?}", r.receipt());
    d.split(['(', ' ', '{']).next().unwrap_or("").to_string()
}

pub fn receipt_json(r: &near_primitives::receipt::Receipt) -> Value {
    json!({
        "id": h(r.receipt_id()),
        "predecessor": hex::encode(r.predecessor_id().as_bytes()),
        "receiver": hex::encode(r.receiver_id().as_bytes()),
        "kind": receipt_kind(r),
        "hash": sha(&borsh::to_vec(r).unwrap()),
    })
}

/// One key's committed changes: the final value (`None` = deleted) and every change's cause.
pub fn change_json(c: &near_primitives::types::RawStateChangesWithTrieKey) -> Value {
    let last = c.changes.last().and_then(|x| x.data.as_ref());
    json!({
        "key": hex::encode(c.trie_key.to_vec()),
        "valueHash": last.map(|v| sha(v)),
        "valueLen": last.map(|v| v.len().to_string()),
        "causes": c.changes.iter().map(|x| format!("{:?}", x.cause)).collect::<Vec<_>>(),
    })
}

/// W01 per-receipt attribution: every committed change of one key in order (cause, value hash and
/// length, `None` = deleted) and the key's pre-state value reference (`None` = absent), read from
/// the witness's own recorded pre-state (`sha256` of the value, as `ValueRef.hash`).
pub fn change_detail_json(c: &near_primitives::types::RawStateChangesWithTrieKey, pre: Option<&near_store::Trie>) -> Value {
    let mut v = change_json(c);
    let key = c.trie_key.to_vec();
    let pre_ref = pre.map(|t| {
        match t.get_optimized_ref(&key, near_store::KeyLookupMode::MemOrTrie, near_store::trie::AccessOptions::NO_SIDE_EFFECTS) {
            Ok(Some(r)) => json!({ "valueHash": h(&r.value_hash()), "valueLen": r.len().to_string() }),
            Ok(None) => json!({ "absent": true }),
            Err(e) => json!({ "error": format!("{e:?}") }),
        }
    });
    if let Value::Object(m) = &mut v {
        m.insert(
            "changes".into(),
            Value::Array(
                c.changes
                    .iter()
                    .map(|x| {
                        json!({
                            "cause": format!("{:?}", x.cause),
                            "valueHash": x.data.as_ref().map(|d| sha(d)),
                            "valueLen": x.data.as_ref().map(|d| d.len().to_string()),
                        })
                    })
                    .collect(),
            ),
        );
        m.insert("pre".into(), pre_ref.unwrap_or(Value::Null));
    }
    v
}

pub(crate) fn observe(client: &Client, rt: &NightshadeRuntime, wb: &[u8], codes: &[Vec<u8>]) -> Result<Value, String> {
    let w = crate::judge::decode_witness(wb, codes)?;
    let em: &dyn EpochManagerAdapter = client.epoch_manager.as_ref();
    let pre = pre_validate_chunk_state_witness(&w, client.chain.chain_store(), client.chain.genesis_block(), em, rt)
        .map_err(|e| format!("pre_validate: {e:?}"))?;
    let (new_chunk_data, block_hash, shard_id) = match pre.main_transition_params {
        MainTransition::Genesis { .. } => return Ok(json!({ "status": "genesis" })),
        MainTransition::NewChunk { new_chunk_data, block_hash, shard_id } => (new_chunk_data, block_hash, shard_id),
    };
    let height = new_chunk_data.block.height;
    // the main transition's pre-state, from the witness's recorded nodes (W01 attribution)
    let pre_trie = match &new_chunk_data.storage_context.storage_data_source {
        near_chain::types::StorageDataSource::Recorded(ps) => {
            Some(near_store::Trie::from_recorded_storage(ps.clone(), new_chunk_data.prev_state_root, false))
        }
        _ => None,
    };
    let epoch_id = em.get_epoch_id(&block_hash).map_err(|e| format!("{e:?}"))?;
    let shard_uid = shard_id_to_uid(em, shard_id, &epoch_id).map_err(|e| format!("{e:?}"))?;
    let span = near_o11y::tracing::debug_span!(target: "client", "w01_observables");
    let res = apply_new_chunk(
        ApplyChunkReason::ValidateChunkStateWitness,
        &span,
        new_chunk_data,
        ShardContext { shard_uid, should_apply_chunk: true },
        rt,
        MaybePinnedMemtrieRoot::no_memtries(),
        None,
    )
    .map_err(|e| format!("apply: {e:?}"))?;
    let a = &res.apply_result;
    let (outcome_root, _) = ApplyChunkResult::compute_outcomes_proof(&a.outcomes);
    let outcomes: Vec<Value> = a
        .outcomes
        .iter()
        .map(|o| {
            let x = &o.outcome;
            json!({
                "id": h(&o.id),
                "executor": hex::encode(x.executor_id.as_bytes()),
                "status": status_json(&x.status),
                "gasBurnt": x.gas_burnt.as_gas().to_string(),
                "tokensBurnt": x.tokens_burnt.as_yoctonear().to_string(),
                "computeUsage": x.compute_usage.map(|c| c.to_string()),
                "logs": x.logs.iter().map(|l| hex::encode(l.as_bytes())).collect::<Vec<_>>(),
                "receiptIds": x.receipt_ids.iter().map(h).collect::<Vec<_>>(),
            })
        })
        .collect();
    // The list the chunk header's outgoing root commits to: across a shard split the validator
    // reassigns the parent's outgoing receipts to the lowest child (`chunk_validation.rs:640-651`).
    let mut committed_receipts = a.outgoing_receipts.clone();
    let witness_key = w.chunk_production_key();
    let witness_layout = em.get_shard_layout(&witness_key.epoch_id).map_err(|e| format!("{e:?}"))?;
    let chunk_layout = em.get_shard_layout(&epoch_id).map_err(|e| format!("{e:?}"))?;
    let reassigned = chunk_layout != witness_layout;
    if reassigned {
        near_chain::ChainStore::reassign_outgoing_receipts_for_resharding(&mut committed_receipts, &witness_layout, witness_key.shard_id, shard_id)
            .map_err(|e| format!("reassign: {e:?}"))?;
    }
    let outgoing: Vec<Value> = committed_receipts.iter().map(receipt_json).collect();
    let outgoing_applied: Option<Vec<Value>> = reassigned.then(|| a.outgoing_receipts.iter().map(receipt_json).collect());
    let changes: Vec<Value> = a.trie_changes.state_changes().iter().map(|c| change_detail_json(c, pre_trie.as_ref())).collect();
    let compute: Option<u64> = a.outcomes.iter().try_fold(0u64, |s, o| o.outcome.compute_usage.map(|c| s + c));
    let store = client.chain.chain_store();
    let stored = near_store::adapter::StoreAdapter::chain_store(&store.store()).get_outcomes_by_block_hash_and_shard_id(&block_hash, shard_id);
    Ok(json!({
        "status": "ok",
        "height": height,
        "shard_id": shard_id.to_string(),
        "block_hash": h(&block_hash),
        "state_root": h(&a.new_root),
        "outcome_root": h(&outcome_root),
        "header_prev_outcome_root": h(&w.chunk_header().prev_outcome_root()),
        "gas_used": a.total_gas_burnt.as_gas().to_string(),
        "balance_burnt": a.total_balance_burnt.as_yoctonear().to_string(),
        "compute_usage": compute.map(|c| c.to_string()),
        "outcomes": outcomes,
        "outgoing_receipts": outgoing,
        "outgoing_receipts_before_reassignment": outgoing_applied,
        "state_changes": changes,
        "store_outcome_ids": stored.iter().map(h).collect::<Vec<_>>(),
    }))
}
