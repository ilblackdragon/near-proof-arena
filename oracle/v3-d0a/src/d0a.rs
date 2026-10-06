//! Independent Rust predicate for the D0a amendments (spec/near-chunk-validation-v0a.md):
//! A1 `c.gas_limit`, A2 `w.proof_routing`, Canon0f `e.sched_canonical`. Used together with
//! the D0 classifier (../v3/src/d0.rs): a case is in D0a iff both return no violation.
//! Uses nearcore's own objects and code (chunk headers, `Receipt::receiver_shard_id`, the
//! tracking node's full state, `Trie::from_recorded_storage` on the witness), not the
//! Lean/Python implementations.

use crate::claim::Built;
use near_client::Client;
use near_primitives::bandwidth_scheduler::BandwidthSchedulerState;
use near_primitives::state::PartialState;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_store::{PartialStorage, Trie};

fn canonical(st: &Option<BandwidthSchedulerState>, layout: &near_primitives::shard_layout::ShardLayout) -> bool {
    match st {
        None => true,
        Some(BandwidthSchedulerState::V1(v1)) => {
            let ids: Vec<_> = layout.shard_ids().collect();
            let want: Vec<_> = ids.iter().flat_map(|s| ids.iter().map(move |r| (*s, *r))).collect();
            let got: Vec<_> = v1.link_allowances.iter().map(|l| (l.sender, l.receiver)).collect();
            got == want
        }
    }
}

pub fn extra(client: &Client, built: &Built, w: &ChunkStateWitness) -> Result<Vec<&'static str>, String> {
    let mut v = Vec::new();
    let b2 = &built.blocks[built.b2];
    if b2.header().is_genesis() {
        return Ok(v);
    }
    let em = client.epoch_manager.as_ref();
    let layout = em.get_shard_layout(b2.header().epoch_id()).map_err(|e| e.to_string())?;
    let idx = layout.get_shard_index(built.shard_id).map_err(|e| e.to_string())?;
    let slot = b2.chunks().get(idx).ok_or("slot")?.clone();
    // A1: chunk gas limit of B2's own slot
    if slot.gas_limit().as_gas() > 1_000_000_000_000_000 {
        v.push("c.gas_limit");
    }
    // A2: every receipt of every source proof (an honest witness holds exactly the used ones)
    let ChunkStateWitness::V2(x) = w;
    'a2: for p in x.source_receipt_proofs.values() {
        for r in &p.0 {
            if r.receiver_shard_id(&layout).map_err(|e| e.to_string())? != built.shard_id {
                v.push("w.proof_routing");
                break 'a2;
            }
        }
    }
    // Canon0f: main pre-state value (tracking node's full state) and every implicit
    // transition's read (nearcore's recorded-storage trie over the witness values)
    let rt = client.runtime_adapter.as_ref();
    let pre = rt
        .get_trie_for_shard(built.shard_id, b2.header().prev_hash(), slot.prev_state_root(), false)
        .map_err(|e| e.to_string())?;
    let mut ok = canonical(&near_store::get_bandwidth_scheduler_state(&pre).map_err(|e| e.to_string())?, &layout);
    let mut root = x.main_state_transition.post_state_root;
    for t in &x.implicit_transitions {
        let PartialState::TrieValues(_) = &t.base_state;
        let trie = Trie::from_recorded_storage(PartialStorage { nodes: t.base_state.clone() }, root, false);
        ok &= canonical(&near_store::get_bandwidth_scheduler_state(&trie).map_err(|e| e.to_string())?, &layout);
        root = t.post_state_root;
    }
    if !ok {
        v.push("e.sched_canonical");
    }
    Ok(v)
}
