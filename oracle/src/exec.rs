//! Execute a case with the real pinned nearcore `Runtime::apply` on an
//! in-memory trie, derive the canonical claim, record the slice witness and
//! check the projection decomposition.

use near_parameters::RuntimeConfigStore;
use near_primitives::apply::ApplyChunkReason;
use near_primitives::bandwidth_scheduler::BlockBandwidthRequests;
use near_primitives::congestion_info::{BlockCongestionInfo, ExtendedCongestionInfo};
use near_primitives::hash::{CryptoHash, hash};
use near_primitives::merkle::merklize;
use near_primitives::receipt::Receipt;
use near_primitives::state::PartialState;
use near_primitives::test_utils::MockEpochInfoProvider;
use near_primitives::transaction::{ExecutionOutcomeWithId, ExecutionStatus};
use near_primitives::types::{EpochId, EpochInfoProvider, Gas, ShardId};
use near_store::ShardTries;
use near_store::test_utils::TestTriesBuilder;
use near_store::trie::AccessOptions;
use node_runtime::{ApplyState, Runtime, SignedValidPeriodTransactions};
use serde_json::json;
use std::collections::BTreeMap;


use crate::enc::{self, Claim, Request};

pub struct Executed {
    pub request: Request,
    pub claim: Option<Claim>,
    pub witness_values: Vec<Vec<u8>>,
    pub nearcore: serde_json::Value,
    /// nearcore behaved "cleanly" (all receipts executed successfully, no
    /// delayed/buffered receipts, only Account + bandwidth-scheduler keys changed,
    /// outgoing receipts == generated refunds, decomposition holds).
    pub clean: bool,
    pub problems: Vec<String>,
}

fn h(x: &CryptoHash) -> String {
    hex::encode(x.as_ref())
}

pub fn receipts_commitment(shard_id: u64, receipts: &[Receipt]) -> [u8; 32] {
    // sha256(borsh((ShardId, Vec<Receipt>))) -- same shape as nearcore's
    // per-shard outgoing-receipts bucket hash (chain.rs build_receipts_hashes).
    hash(&borsh::to_vec(&(ShardId::new(shard_id), receipts)).unwrap()).0
}

pub fn refunds_commitment(refunds: &[Receipt]) -> [u8; 32] {
    hash(&borsh::to_vec(&refunds.to_vec()).unwrap()).0
}

pub fn run(mut req: Request, state: &BTreeMap<Vec<u8>, Vec<u8>>) -> Executed {
    let mut problems = vec![];
    let config_store = RuntimeConfigStore::new(None);
    let config = config_store.get_config(req.protocol_version).clone();

    let epoch_info_provider = MockEpochInfoProvider::default();
    let shard_layout = epoch_info_provider.shard_layout(&EpochId::default()).unwrap();
    let shard_uid = shard_layout.shard_uids().next().unwrap();
    if shard_uid.shard_id() != ShardId::new(req.shard_id) {
        problems.push(format!("oracle only supports the single-shard layout (shard 0), got {}", req.shard_id));
    }

    // ---- pre-state ----
    let tries: ShardTries = TestTriesBuilder::new().build();
    let empty = tries.get_trie_for_shard(shard_uid, CryptoHash::default());
    let changes: Vec<(Vec<u8>, Option<Vec<u8>>)> =
        state.iter().map(|(k, v)| (k.clone(), Some(v.clone()))).collect();
    let tc = empty.update(changes, AccessOptions::DEFAULT).unwrap();
    let mut su = tries.store_update();
    let pre_root = tries.apply_all(&tc, shard_uid, &mut su);
    su.commit();
    req.pre_state_root = pre_root;

    let congestion_info = BlockCongestionInfo::new(
        shard_layout.shard_ids().map(|s| (s, ExtendedCongestionInfo::default())).collect(),
    );
    let apply_state = ApplyState {
        apply_reason: ApplyChunkReason::UpdateTrackedShard,
        block_height: req.block_height,
        prev_block_hash: CryptoHash::default(),
        shard_id: shard_uid.shard_id(),
        epoch_id: EpochId::default(),
        epoch_height: 0,
        gas_price: near_primitives::types::Balance::from_yoctonear(req.block_gas_price),
        block_timestamp: 1_000,
        gas_limit: Some(Gas::from_gas(req.gas_limit)),
        random_seed: CryptoHash::default(),
        current_protocol_version: req.protocol_version,
        config: config.clone(),
        next_wasm_config: None,
        cache: None,
        trie_access_tracker_state: Default::default(),
        is_new_chunk: true,
        save_receipt_to_tx: false,
        congestion_info,
        bandwidth_requests: BlockBandwidthRequests::empty(),
        on_post_state_ready: None,
    };

    // ---- slice witness: nodes + values read on the paths to every receiver's
    // Account key in the pre-trie (nearcore's own TrieRecorder) ----
    let rec = tries.get_trie_for_shard(shard_uid, pre_root).recording_reads_new_recorder();
    for r in &req.receipts {
        let _ = rec.get(&crate::domain::account_key(r.receiver_id().as_str()), AccessOptions::DEFAULT).unwrap();
    }
    let proof = rec.recorded_storage().unwrap();
    let PartialState::TrieValues(values) = &proof.nodes;
    let witness_values: Vec<Vec<u8>> = values.iter().map(|v| v.to_vec()).collect();

    // ---- the real Runtime::apply (recording, as validators do) ----
    let trie = tries.get_trie_for_shard(shard_uid, pre_root).recording_reads_new_recorder();
    let t0 = std::time::Instant::now();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        Runtime::new().apply(
            trie,
            &None,
            &apply_state,
            &req.receipts,
            SignedValidPeriodTransactions::empty(),
            &epoch_info_provider,
            Default::default(),
        )
    }));
    let apply_ns = t0.elapsed().as_nanos() as u64;

    let result = match res {
        Err(_) => {
            return Executed {
                request: req,
                claim: None,
                witness_values: witness_values.clone(),
                nearcore: json!({"apply": "panicked", "apply_ns": apply_ns}),
                clean: false,
                problems: vec!["Runtime::apply panicked".into()],
            };
        }
        Ok(Err(e)) => {
            return Executed {
                request: req,
                claim: None,
                witness_values: witness_values.clone(),
                nearcore: json!({"apply": "error", "error": format!("{e:?}"), "apply_ns": apply_ns}),
                clean: false,
                problems: vec![format!("Runtime::apply error: {e:?}")],
            };
        }
        Ok(Ok(r)) => r,
    };

    // ---- observe ----
    let n = req.receipts.len();
    if result.outcomes.len() != n {
        problems.push(format!("{} outcomes for {} receipts", result.outcomes.len(), n));
    }
    if result.delayed_receipts_count != 0 {
        problems.push(format!("{} delayed receipts", result.delayed_receipts_count));
    }
    let mut statuses = vec![];
    for (o, r) in result.outcomes.iter().zip(req.receipts.iter()) {
        if o.id != *r.receipt_id() {
            problems.push("outcome order != receipt order".into());
        }
        match &o.outcome.status {
            ExecutionStatus::SuccessValue(v) if v.is_empty() => statuses.push("SuccessValue([])".to_string()),
            s => {
                problems.push(format!("receipt {} status {:?}", h(&o.id), s));
                statuses.push(format!("{s:?}"));
            }
        }
        if !o.outcome.logs.is_empty() {
            problems.push("logs not empty".into());
        }
    }
    let hashes: Vec<Vec<CryptoHash>> =
        result.outcomes.iter().map(ExecutionOutcomeWithId::to_hashes).collect();
    let (outcome_root, _) = merklize(&hashes);
    let refund_ids: Vec<CryptoHash> =
        result.outcomes.iter().flat_map(|o| o.outcome.receipt_ids.iter().cloned()).collect();
    let out_ids: Vec<CryptoHash> = result.outgoing_receipts.iter().map(|r| *r.receipt_id()).collect();
    if refund_ids != out_ids {
        problems.push(format!(
            "outgoing receipts ({}) != outcome receipt_ids ({}) (buffered?)",
            out_ids.len(),
            refund_ids.len()
        ));
    }
    let gas_total: u64 = result.outcomes.iter().map(|o| o.outcome.gas_burnt.as_gas()).sum();
    let tokens_total: u128 =
        result.outcomes.iter().map(|o| o.outcome.tokens_burnt.as_yoctonear()).sum();
    if tokens_total != result.stats.balance.tx_burnt_amount.as_yoctonear() {
        problems.push("sum(tokens_burnt) != stats.balance.tx_burnt_amount".into());
    }
    let b = &result.stats.balance;
    if !b.other_burnt_amount.is_zero() || !b.gas_deficit_amount.is_zero() || !b.slashed_burnt_amount.is_zero() {
        problems.push(format!("unexpected balance stats {b:?}"));
    }

    // ---- state changes: Account vs other ----
    let all: Vec<(Vec<u8>, Option<Vec<u8>>)> = result
        .state_changes
        .iter()
        .map(|ch| (ch.trie_key.to_vec(), ch.changes.last().unwrap().data.clone()))
        .collect();
    let account_changes: Vec<_> = all.iter().filter(|(k, _)| k[0] == 0).cloned().collect();
    let other: Vec<String> =
        all.iter().filter(|(k, _)| k[0] != 0).map(|(k, _)| hex::encode(k)).collect();
    if other.iter().any(|k| k != "0f") {
        problems.push(format!("non-Account keys other than bandwidth scheduler changed: {other:?}"));
    }
    for (k, v) in &account_changes {
        match v {
            None => problems.push("account deleted".into()),
            Some(v) if v.len() != 72 => problems.push("account value length changed".into()),
            _ => {}
        }
        if !state.contains_key(k) {
            problems.push("account key inserted".into());
        }
    }
    let base = tries.get_trie_for_shard(shard_uid, pre_root);
    let slice_root = base.update(account_changes.clone(), AccessOptions::DEFAULT).unwrap().new_root;
    let full_again = base.update(all.clone(), AccessOptions::DEFAULT).unwrap().new_root;
    let decomposition_ok = full_again == result.state_root;
    if !decomposition_ok {
        problems.push("decomposition failed: pre ⊕ changes != Runtime::apply root".into());
    }

    // witness-only re-execution of the slice update (nearcore's own partial-trie path)
    if !account_changes.is_empty() {
        let wt = near_store::Trie::from_recorded_storage(proof.clone(), pre_root, false);
        let r3 = wt.update(account_changes.clone(), AccessOptions::DEFAULT).unwrap().new_root;
        if r3 != slice_root {
            problems.push("witness-only slice root mismatch".into());
        }
    }

    let full_recorded = result.proof.as_ref().map(|p| {
        let PartialState::TrieValues(v) = &p.nodes;
        v.iter().map(|x| x.len()).sum::<usize>()
    });

    let claim = Claim {
        protocol_version: req.protocol_version,
        chain_id: req.chain_id.clone(),
        shard_id: req.shard_id,
        block_height: req.block_height,
        block_gas_price: req.block_gas_price,
        gas_limit: req.gas_limit,
        pre_state_root: pre_root.0,
        receipt_count: n as u32,
        receipts_commitment: receipts_commitment(req.shard_id, &req.receipts),
        slice_post_root: slice_root.0,
        outcome_root: outcome_root.0,
        refund_count: result.outgoing_receipts.len() as u32,
        refund_receipts_commitment: refunds_commitment(&result.outgoing_receipts),
        gas_burnt_total: gas_total,
        tokens_burnt_total: tokens_total,
    };
    let nearcore = json!({
        "apply": "ok",
        "apply_ns": apply_ns,
        "full_apply_state_root": h(&result.state_root),
        "slice_post_root": h(&slice_root),
        "decomposition_ok": decomposition_ok,
        "non_account_keys_changed": other,
        "outcome_statuses": statuses.iter().fold(std::collections::BTreeMap::<String, usize>::new(), |mut m, s| { *m.entry(s.clone()).or_default() += 1; m }),
        "outgoing_receipts": result.outgoing_receipts.len(),
        "delayed_receipts_count": result.delayed_receipts_count,
        "tx_burnt_amount": result.stats.balance.tx_burnt_amount.as_yoctonear().to_string(),
        "other_burnt_amount": result.stats.balance.other_burnt_amount.as_yoctonear().to_string(),
        "full_apply_recorded_bytes": full_recorded,
        "slice_witness_values": witness_values.len(),
        "slice_witness_bytes": witness_values.iter().map(|v| v.len()).sum::<usize>(),
    });
    let clean = problems.is_empty();
    let _ = enc::CLAIM_FORMAT;
    Executed { request: req, claim: Some(claim), witness_values, nearcore, clean, problems }
}
