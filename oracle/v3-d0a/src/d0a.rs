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

// ---------------- A7 `w.unfolded` ----------------

/// A7 bound of the challenge instance (`NearSpecV3.B0`).
pub const B0: u64 = 3_000_000;
//
// Independent computation of `unfoldBytes` (spec/near-chunk-validation-v0a.md §2.4) on
// nearcore's own node type (`RawTrieNodeWithSize` borsh) and stores: the pre-trie nodes come
// from the witness's recorded values (by hash), the post-trie nodes from the tracking node's
// State column. Keys are the trie keys the D0 run reads (nearcore `TrieKey::to_vec`).

use near_primitives::hash::{CryptoHash, hash as nhash};
use near_primitives::trie_key::TrieKey;
use near_store::{RawTrieNode, RawTrieNodeWithSize, TrieStorage};
use std::collections::HashMap;

fn nibs(b: &[u8]) -> Vec<u8> {
    b.iter().flat_map(|x| [x >> 4, x & 15]).collect()
}

/// hex-prefix decode (`NibbleSlice::from_encoded`)
fn hp(e: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    if e.is_empty() {
        return out;
    }
    if e[0] & 0x10 != 0 {
        out.push(e[0] & 15);
    }
    out.extend(nibs(&e[1..]));
    out
}

trait Store {
    fn raw(&self, h: &CryptoHash) -> Option<Vec<u8>>;
}
struct MapStore(HashMap<CryptoHash, Vec<u8>>);
impl Store for MapStore {
    fn raw(&self, h: &CryptoHash) -> Option<Vec<u8>> {
        self.0.get(h).cloned()
    }
}
struct DbStore(near_store::TrieDBStorage);
impl Store for DbStore {
    fn raw(&self, h: &CryptoHash) -> Option<Vec<u8>> {
        self.0.retrieve_raw_bytes(h).ok().map(|x| x.to_vec())
    }
}

fn node(st: &dyn Store, h: &CryptoHash) -> Option<(Vec<u8>, RawTrieNode)> {
    let raw = st.raw(h)?;
    let n: RawTrieNodeWithSize = borsh::from_slice(&raw).ok()?;
    Some((raw, n.node))
}

fn value(st: &dyn Store, len: u32, h: &CryptoHash, want: bool) -> u64 {
    if !want {
        return 0;
    }
    match st.raw(h) {
        Some(v) if v.len() == len as usize => v.len() as u64,
        _ => 0,
    }
}

fn unfold_pre(st: &dyn Store, h: &CryptoHash, keys: &[Vec<u8>]) -> u64 {
    if keys.is_empty() {
        return 0;
    }
    let Some((raw, n)) = node(st, h) else { return 0 };
    let mut tot = raw.len() as u64;
    match n {
        RawTrieNode::Leaf(k, v) => {
            let k = hp(&k);
            tot += value(st, v.length, &v.hash, keys.iter().any(|x| *x == k));
        }
        RawTrieNode::Extension(k, c) => {
            let k = hp(&k);
            let sub: Vec<_> = keys.iter().filter(|x| x.starts_with(&k)).map(|x| x[k.len()..].to_vec()).collect();
            tot += unfold_pre(st, &c, &sub);
        }
        RawTrieNode::BranchNoValue(cs) => tot += pre_children(st, &cs.0, keys),
        RawTrieNode::BranchWithValue(v, cs) => {
            tot += value(st, v.length, &v.hash, keys.iter().any(|x| x.is_empty()));
            tot += pre_children(st, &cs.0, keys);
        }
    }
    tot
}

fn pre_children(st: &dyn Store, cs: &[Option<CryptoHash>; 16], keys: &[Vec<u8>]) -> u64 {
    let mut tot = 0;
    for (i, c) in cs.iter().enumerate() {
        if let Some(c) = c {
            let sub: Vec<_> = keys.iter().filter(|x| x.first() == Some(&(i as u8))).map(|x| x[1..].to_vec()).collect();
            tot += unfold_pre(st, c, &sub);
        }
    }
    tot
}

fn slot_diff(pre: Option<(u32, CryptoHash)>, post_st: &dyn Store, len: u32, h: &CryptoHash, want: bool) -> u64 {
    if pre == Some((len, *h)) { 0 } else { value(post_st, len, h, want) }
}

fn unfold_diff(pre_st: &dyn Store, hpre: Option<CryptoHash>, post_st: &dyn Store, hpost: &CryptoHash, keys: &[Vec<u8>]) -> u64 {
    if keys.is_empty() {
        return 0;
    }
    let Some((raw, n)) = node(post_st, hpost) else { return 0 };
    let pn = hpre.and_then(|h| node(pre_st, &h));
    if let Some((praw, _)) = &pn {
        if *praw == raw {
            return 0;
        }
    }
    let pn = pn.map(|x| x.1);
    let mut tot = raw.len() as u64;
    match n {
        RawTrieNode::Leaf(k, v) => {
            let kk = hp(&k);
            let pv = match &pn {
                Some(RawTrieNode::Leaf(pk, pv)) if hp(pk) == kk => Some((pv.length, pv.hash)),
                _ => None,
            };
            tot += slot_diff(pv, post_st, v.length, &v.hash, keys.iter().any(|x| *x == kk));
        }
        RawTrieNode::Extension(k, c) => {
            let kk = hp(&k);
            let pc = match &pn {
                Some(RawTrieNode::Extension(pk, pc)) if hp(pk) == kk => Some(*pc),
                _ => None,
            };
            let sub: Vec<_> = keys.iter().filter(|x| x.starts_with(&kk)).map(|x| x[kk.len()..].to_vec()).collect();
            tot += unfold_diff(pre_st, pc, post_st, &c, &sub);
        }
        RawTrieNode::BranchNoValue(cs) => tot += branch_diff(pre_st, &pn, post_st, None, &cs.0, keys),
        RawTrieNode::BranchWithValue(v, cs) => tot += branch_diff(pre_st, &pn, post_st, Some((v.length, v.hash)), &cs.0, keys),
    }
    tot
}

fn branch_diff(pre_st: &dyn Store, pn: &Option<RawTrieNode>, post_st: &dyn Store, v: Option<(u32, CryptoHash)>,
               cs: &[Option<CryptoHash>; 16], keys: &[Vec<u8>]) -> u64 {
    let (pv, pcs): (Option<(u32, CryptoHash)>, Option<[Option<CryptoHash>; 16]>) = match pn {
        Some(RawTrieNode::BranchNoValue(c)) => (None, Some(c.0)),
        Some(RawTrieNode::BranchWithValue(x, c)) => (Some((x.length, x.hash)), Some(c.0)),
        _ => (None, None),
    };
    let mut tot = 0;
    if let Some((len, h)) = v {
        tot += slot_diff(pv, post_st, len, &h, keys.iter().any(|x| x.is_empty()));
    }
    for (i, c) in cs.iter().enumerate() {
        if let Some(c) = c {
            let sub: Vec<_> = keys.iter().filter(|x| x.first() == Some(&(i as u8))).map(|x| x[1..].to_vec()).collect();
            let pc = pcs.and_then(|p| p[i]);
            tot += unfold_diff(pre_st, pc, post_st, c, &sub);
        }
    }
    tot
}

/// `unfoldBytes` of an honest case (None if B2 is genesis: not in D0).
pub fn unfold_bytes(client: &Client, built: &Built, w: &ChunkStateWitness) -> Result<Option<u64>, String> {
    use near_chain::stateless_validation::chunk_validation::MainTransition;
    use near_primitives::receipt::{BufferedReceiptIndices, ReceiptEnum};
    use near_store::adapter::StoreAdapter;
    let b2 = &built.blocks[built.b2];
    if b2.header().is_genesis() {
        return Ok(None);
    }
    let em = client.epoch_manager.as_ref();
    let layout = em.get_shard_layout(b2.header().epoch_id()).map_err(|e| e.to_string())?;
    let idx = layout.get_shard_index(built.shard_id).map_err(|e| e.to_string())?;
    let slot = b2.chunks().get(idx).ok_or("slot")?.clone();
    let pre = crate::judge::pre_validate(client, w)?;
    let receipts = match pre.main_transition_params {
        MainTransition::NewChunk { new_chunk_data, .. } => new_chunk_data.receipts,
        MainTransition::Genesis { .. } => vec![],
    };
    let rt = client.runtime_adapter.as_ref();
    let pre_trie = rt
        .get_trie_for_shard(built.shard_id, b2.header().prev_hash(), slot.prev_state_root(), false)
        .map_err(|e| e.to_string())?;
    let bufs: Option<BufferedReceiptIndices> =
        near_store::get(&pre_trie, &TrieKey::BufferedReceiptIndices).map_err(|e| e.to_string())?;
    let mut keys: Vec<TrieKey> = vec![
        TrieKey::DelayedReceiptIndices,
        TrieKey::BandwidthSchedulerState,
        TrieKey::BufferedReceiptIndices,
        TrieKey::PromiseYieldIndices,
    ];
    for s in bufs.map(|b| b.shard_buffers.keys().cloned().collect::<Vec<_>>()).unwrap_or_default() {
        keys.push(TrieKey::BufferedReceiptGroupsQueueData { receiving_shard: s });
    }
    for r in &receipts {
        keys.push(TrieKey::Account { account_id: r.receiver_id().clone() });
        if let ReceiptEnum::Action(ar) = r.receipt() {
            if r.predecessor_id().is_system() && &ar.signer_id == r.receiver_id() {
                keys.push(TrieKey::AccessKey { account_id: r.receiver_id().clone(), key_handle: ar.signer_public_key.clone().into() });
            }
        }
    }
    let main_keys: Vec<Vec<u8>> = keys.iter().map(|k| nibs(&k.to_vec())).collect();
    let imp_keys: Vec<Vec<u8>> =
        [TrieKey::DelayedReceiptIndices, TrieKey::BandwidthSchedulerState].iter().map(|k| nibs(&k.to_vec())).collect();
    let uid = near_primitives::shard_layout::ShardUId::from_shard_id_and_layout(built.shard_id, &layout);
    let db = DbStore(near_store::TrieDBStorage::new(client.chain.chain_store().store().trie_store(), uid));
    let ChunkStateWitness::V2(x) = w;
    let mapst = |t: &near_primitives::stateless_validation::state_witness::ChunkStateTransition| {
        let PartialState::TrieValues(vals) = &t.base_state;
        MapStore(vals.iter().map(|v| (nhash(v), v.to_vec())).collect())
    };
    let mut tot = 0u64;
    let m = mapst(&x.main_state_transition);
    tot += unfold_pre(&m, &slot.prev_state_root(), &main_keys);
    tot += unfold_diff(&m, Some(slot.prev_state_root()), &db, &x.main_state_transition.post_state_root, &main_keys);
    let mut root = x.main_state_transition.post_state_root;
    for t in &x.implicit_transitions {
        let s = mapst(t);
        tot += unfold_pre(&s, &root, &imp_keys);
        tot += unfold_diff(&s, Some(root), &db, &t.post_state_root, &imp_keys);
        root = t.post_state_root;
    }
    Ok(Some(tot))
}
