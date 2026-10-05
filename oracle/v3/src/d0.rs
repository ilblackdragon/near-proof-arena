//! Independent Rust predicate for domain D0 (spec/near-chunk-validation-v0.md
//! §6). Classifies an honest (claim, witness) pair; returns the list of
//! violated D0 conditions (empty = in D0). Uses the oracle client's full state
//! and stored outcomes, not the Lean/Python implementations.

use crate::claim::Built;
use near_chain::stateless_validation::chunk_validation::MainTransition;
use near_client::Client;
use near_primitives::account::AccessKeyPermission;
use near_primitives::action::Action;
use near_primitives::receipt::{
    BufferedReceiptIndices, DelayedReceiptIndices, PromiseYieldIndices, ReceiptEnum,
};
use near_primitives::sharding::ShardChunkHeader;
use near_primitives::state::PartialState;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::trie_key::TrieKey;
use near_primitives::views::ExecutionStatusView;
use near_primitives_core::account::id::AccountType;
use near_store::Trie;
use std::collections::HashSet;

fn queues_empty(trie: &Trie) -> Result<(bool, bool, bool), String> {
    let e = |x: near_store::StorageError| x.to_string();
    let d: Option<DelayedReceiptIndices> =
        near_store::get(trie, &TrieKey::DelayedReceiptIndices).map_err(e)?;
    let b: Option<BufferedReceiptIndices> =
        near_store::get(trie, &TrieKey::BufferedReceiptIndices).map_err(e)?;
    let y: Option<PromiseYieldIndices> =
        near_store::get(trie, &TrieKey::PromiseYieldIndices).map_err(e)?;
    let d_empty = d.map_or(true, |d| d.first_index == d.next_available_index);
    let b_empty = b.map_or(true, |b| {
        b.shard_buffers.values().all(|q| q.first_index == q.next_available_index)
    });
    let y_empty = y.map_or(true, |y| y.first_index == y.next_available_index);
    Ok((d_empty, b_empty, y_empty))
}

/// Does this client hold the ChunkExtra of the main transition (it tracked the shard at B2)?
pub fn tracks(client: &Client, built: &Built) -> bool {
    let b2 = &built.blocks[built.b2];
    let Ok(layout) = client.epoch_manager.get_shard_layout(b2.header().epoch_id()) else { return false };
    let uid = near_primitives::shard_layout::ShardUId::from_shard_id_and_layout(built.shard_id, &layout);
    client.chain.get_chunk_extra(b2.hash(), &uid).is_ok()
}

pub fn classify(
    client: &Client,
    built: &Built,
    w: &ChunkStateWitness,
    witness_bytes_len: usize,
    n_codes: usize,
) -> Result<Vec<&'static str>, String> {
    let mut v: Vec<&'static str> = Vec::new();
    let c = &built.claim;
    let mut add = |s: &'static str| {
        if !v.contains(&s) {
            v.push(s)
        }
    };
    // ---- claim level
    if c.protocol_version != 86 {
        add("c.pv86");
    }
    let single = c.epochs.len() == 1
        && built.blocks.iter().all(|b| b.header().epoch_id().0.0 == c.epoch_id)
        && c.epoch_start_after.iter().all(|f| *f == 0);
    if !single {
        add("c.single_epoch");
    }
    let layout: near_primitives::shard_layout::ShardLayout =
        borsh::from_slice(&c.epochs[0].shard_layout).map_err(|e| e.to_string())?;
    let nshards = layout.shard_ids().count();
    if !(1..=64).contains(&nshards)
        || !matches!(layout, near_primitives::shard_layout::ShardLayout::V2(_) | near_primitives::shard_layout::ShardLayout::V3(_))
    {
        add("c.layout");
    }
    let inner_ok = |b: &[u8]| matches!(b.first(), Some(3) | Some(4));
    if c.blocks.iter().any(|b| b.header_version != 5 || b.slots.iter().any(|s| !inner_ok(&s.inner)))
        || !inner_ok(&c.chunk_inner)
    {
        add("c.headers");
    }
    if c.apply_facts.iter().any(|f| f.validator_update.is_some() || f.split_gate.is_some()) {
        add("c.no_split_gate");
    }
    let b2 = &built.blocks[built.b2];
    if b2.header().is_genesis() {
        add("c.not_genesis");
    }
    if !c.tx_valid.is_empty() {
        add("c.no_tx_flags");
    }
    if c.blocks.len() > 32 {
        add("c.segment");
    }
    // ---- witness level
    if !w.transactions().is_empty() || !w.new_transactions().is_empty() {
        add("w.no_txs");
    }
    if n_codes != 0 {
        add("w.no_code");
    }
    let PartialState::TrieValues(vals) = &w.main_state_transition().base_state;
    let base_bytes: usize = vals.iter().map(|x| x.len()).sum();
    if witness_bytes_len > 8 * 1024 * 1024 || base_bytes > 3_000_000 {
        add("w.size");
    }
    if b2.header().is_genesis() {
        return Ok(v);
    }
    // ---- main transition: receipts and execution
    let em = client.epoch_manager.as_ref();
    let shard_layout = em.get_shard_layout(b2.header().epoch_id()).map_err(|e| e.to_string())?;
    let shard_id = {
        // shard of the main transition (no resharding in oracle chains)
        built.shard_id
    };
    let idx = shard_layout.get_shard_index(shard_id).map_err(|e| e.to_string())?;
    let slot = b2.chunks().get(idx).ok_or("slot")?.clone();
    let ci = slot.congestion_info();
    if ci.delayed_receipts_gas() != 0 || ci.buffered_receipts_gas() != 0 || ci.receipt_bytes() != 0 {
        add("c.own_congestion_zero");
    }
    let pre = crate::judge::pre_validate(client, w)?;
    let receipts = match pre.main_transition_params {
        MainTransition::NewChunk { new_chunk_data, .. } => new_chunk_data.receipts,
        MainTransition::Genesis { .. } => vec![],
    };
    let rt = client.runtime_adapter.as_ref();
    let pre_root = slot.prev_state_root();
    let pre_trie = rt
        .get_trie_for_shard(shard_id, b2.header().prev_hash(), pre_root, false)
        .map_err(|e| e.to_string())?;
    let shard_uid = near_primitives::shard_layout::ShardUId::from_shard_id_and_layout(shard_id, &shard_layout);
    let extra = client.chain.get_chunk_extra(b2.hash(), &shard_uid).map_err(|e| e.to_string())?;
    let post_trie = rt
        .get_trie_for_shard(shard_id, b2.hash(), *extra.state_root(), false)
        .map_err(|e| e.to_string())?;
    let (d0, b0, y0) = queues_empty(&pre_trie)?;
    if !(d0 && b0 && y0) {
        add("e.queues_empty");
    }
    let (d1, b1, _y1) = queues_empty(&post_trie)?;
    if !d1 {
        add("e.compute");
    }
    if !b1 {
        add("e.forwarded");
    }
    let mut ids = HashSet::new();
    for r in &receipts {
        if !ids.insert(*r.receipt_id()) {
            add("e.distinct_ids");
        }
        let ReceiptEnum::Action(ar) = r.receipt() else {
            add("r.shape");
            continue;
        };
        let shape_ok = ar.actions.len() == 1
            && matches!(ar.actions[0], Action::Transfer(_))
            && ar.input_data_ids.is_empty()
            && ar.output_data_receivers.is_empty()
            && matches!(
                ar.signer_public_key.key_type(),
                near_crypto::KeyType::ED25519 | near_crypto::KeyType::SECP256K1
            )
            && r.receiver_id().get_account_type() == AccountType::NamedAccount;
        if !shape_ok {
            add("r.shape");
            continue;
        }
        // refund key reads (lib.rs:2899-2919): gas refund = system predecessor and signer == receiver
        if r.predecessor_id().is_system() && &ar.signer_id == r.receiver_id() {
            let ak = near_store::get_access_key(&pre_trie, r.receiver_id(), &ar.signer_public_key)
                .map_err(|e| e.to_string())?;
            let ok = match ak {
                None => true,
                Some(k) => k.gas_key_info().is_none() && matches!(k.permission, AccessKeyPermission::FullAccess),
            };
            if !ok {
                add("r.refunds");
            }
        }
        // receiver exists as 72-byte AccountV1 in the pre-state, and the receipt succeeded in B2
        let acc_raw = pre_trie
            .get(&TrieKey::Account { account_id: r.receiver_id().clone() }.to_vec(), near_store::trie::AccessOptions::DEFAULT)
            .map_err(|e| e.to_string())?;
        let mut success = matches!(acc_raw.as_ref().map(|a| a.len()), Some(72));
        let outs = client.chain.chain_store().get_outcomes_by_id(r.receipt_id()).map_err(|e| e.to_string())?;
        let out = outs.into_iter().find(|o| &o.block_hash == b2.hash());
        match out {
            Some(o) => {
                let st: ExecutionStatusView = o.outcome_with_id.outcome.status.into();
                if !matches!(st, ExecutionStatusView::SuccessValue(_)) {
                    success = false;
                }
            }
            None => success = false,
        }
        if !success {
            add("r.success");
        }
    }
    let _ = ShardChunkHeader::is_genesis; // keep import used across versions
    Ok(v)
}
