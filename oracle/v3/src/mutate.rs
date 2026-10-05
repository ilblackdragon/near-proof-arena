//! Negative (and non-obvious positive) cases derived from an honest D0 case.
//! `Judge::Nearcore` mutants are judged by nearcore's validator on the mutated
//! witness (with the mutated claim's Reed–Solomon parameters); `Judge::Claim`
//! mutants break the claim-v3 hash/consistency discipline and are false by the
//! format's definition (nearcore never sees such a context).

use crate::enc::{BlockRec, Claim};
use near_primitives::hash::CryptoHash;
use near_primitives::sharding::{ChunkHash, ReceiptProof, ShardChunkHeader};
use near_primitives::state::PartialState;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use rand::Rng;
use rand::rngs::StdRng;

pub enum Judge {
    Nearcore,
    Claim,
}

pub struct Mutant {
    pub name: String,
    pub claim: Claim,
    pub witness: Vec<u8>,
    pub judge: Judge,
}

fn v2(w: &mut ChunkStateWitness) -> &mut near_primitives::stateless_validation::state_witness::ChunkStateWitnessV2 {
    match w {
        ChunkStateWitness::V2(b) => b,
    }
}

/// Encode a witness with an explicit list of (possibly duplicated, unsorted)
/// source-receipt-proof entries — the borsh layout of ChunkStateWitness::V2
/// with the HashMap written entry by entry.
pub fn encode_with_entries(w: &ChunkStateWitness, entries: &[(ChunkHash, ReceiptProof)]) -> Vec<u8> {
    let ChunkStateWitness::V2(x) = w;
    let mut out = vec![1u8];
    out.extend(borsh::to_vec(&x.epoch_id).unwrap());
    out.extend(borsh::to_vec(&x.chunk_header).unwrap());
    out.extend(borsh::to_vec(&x.main_state_transition).unwrap());
    out.extend((entries.len() as u32).to_le_bytes());
    for (k, v) in entries {
        out.extend(borsh::to_vec(k).unwrap());
        out.extend(borsh::to_vec(v).unwrap());
    }
    out.extend(borsh::to_vec(&x.applied_receipts_hash).unwrap());
    out.extend(borsh::to_vec(&x.transactions).unwrap());
    out.extend(borsh::to_vec(&x.implicit_transitions).unwrap());
    out.extend(borsh::to_vec(&x.new_transactions).unwrap());
    out
}

fn with_header_inner(w: &ChunkStateWitness, inner: &[u8]) -> Option<ChunkStateWitness> {
    let ShardChunkHeader::V3(h) = w.chunk_header() else { return None };
    let mut hb = vec![2u8];
    hb.extend_from_slice(inner);
    hb.extend(h.height_included.to_le_bytes());
    hb.extend(borsh::to_vec(&h.signature).unwrap());
    let nh: ShardChunkHeader = borsh::from_slice(&hb).ok()?;
    let mut w2 = w.clone();
    v2(&mut w2).chunk_header = nh;
    Some(w2)
}

/// Flip/alter receipt bytes inside a proof (first receipt's receipt_id).
fn corrupt_proof(p: &ReceiptProof) -> Option<ReceiptProof> {
    if p.0.is_empty() {
        let mut q = p.clone();
        q.1.to_shard_id = near_primitives::types::ShardId::new(u64::from_le_bytes(q.1.to_shard_id.to_le_bytes()) ^ 1);
        return Some(q);
    }
    let mut b = borsh::to_vec(p).unwrap();
    // Vec<Receipt>: u32 count, then ReceiptV0 = AccountId(u32 len‖bytes) predecessor, receiver, [32] id
    let mut off = 4;
    let l1 = u32::from_le_bytes(b[off..off + 4].try_into().unwrap()) as usize;
    off += 4 + l1;
    let l2 = u32::from_le_bytes(b[off..off + 4].try_into().unwrap()) as usize;
    off += 4 + l2;
    b[off] ^= 0x01;
    borsh::from_slice(&b).ok()
}

pub fn mutants(
    claim: &Claim,
    w: &ChunkStateWitness,
    parent_of_last: Option<BlockRec>,
    rng: &mut StdRng,
) -> Vec<Mutant> {
    let mut out = Vec::new();
    let enc = |w: &ChunkStateWitness| borsh::to_vec(w).unwrap();
    let push = |out: &mut Vec<Mutant>, name: &str, claim: Claim, witness: Vec<u8>, judge: Judge| {
        out.push(Mutant { name: name.to_string(), claim, witness, judge })
    };

    // ---- endorsed header (claim.chunk_inner and witness header changed together)
    let inner = claim.chunk_inner.clone();
    let mut hdr = |name: &str, f: &dyn Fn(&mut Vec<u8>) -> bool| {
        let mut b = inner.clone();
        if !f(&mut b) {
            return;
        }
        if let Some(w2) = with_header_inner(w, &b) {
            let mut c2 = claim.clone();
            c2.chunk_inner = b;
            out.push(Mutant { name: name.into(), claim: c2, witness: enc(&w2), judge: Judge::Nearcore });
        }
    };
    for (name, off) in [
        ("hdr.prev_state_root", 33usize),
        ("hdr.prev_outcome_root", 65),
        ("hdr.encoded_merkle_root", 97),
        ("hdr.encoded_length", 129),
        ("hdr.height_created", 137),
        ("hdr.prev_gas_used", 153),
        ("hdr.gas_limit", 161),
        ("hdr.prev_balance_burnt", 169),
        ("hdr.prev_outgoing_receipts_root", 185),
        ("hdr.tx_root", 217),
    ] {
        hdr(name, &|b: &mut Vec<u8>| {
            b[off] ^= 0x01;
            true
        });
    }
    let nprop = u32::from_le_bytes(inner[249..253].try_into().unwrap());
    if nprop == 0 {
        // congestion: tag@253 delayed@254 buffered@270 bytes@286 allowed@294; bandwidth tag@296 count@297
        hdr("hdr.congestion.allowed_shard", &|b| {
            b[294] ^= 0x01;
            true
        });
        hdr("hdr.congestion.delayed_gas", &|b| {
            b[254] ^= 0x01;
            true
        });
        hdr("hdr.congestion.receipt_bytes", &|b| {
            b[286] ^= 0x01;
            true
        });
        hdr("hdr.bandwidth_requests.add", &|b| {
            let n = u32::from_le_bytes(b[297..301].try_into().unwrap());
            b[297..301].copy_from_slice(&(n + 1).to_le_bytes());
            let pos = 301 + 7 * n as usize;
            b.splice(pos..pos, [0u8, 0, 1, 0, 0, 0, 0]);
            true
        });
        hdr("hdr.proposals.add", &|b| {
            b[249..253].copy_from_slice(&1u32.to_le_bytes());
            let mut p = vec![0u8];
            p.extend(4u32.to_le_bytes());
            p.extend(b"s0a0");
            p.push(0);
            p.extend([7u8; 32]);
            p.extend(1u128.to_le_bytes());
            b.splice(253..253, p);
            true
        });
        if inner[0] == 4 && *inner.last().unwrap() == 0 {
            hdr("hdr.proposed_split.some", &|b| {
                b.pop();
                b.push(1);
                b.extend(4u32.to_le_bytes());
                b.extend(b"s1a0");
                b.extend(1u64.to_le_bytes());
                b.extend(1u64.to_le_bytes());
                true
            });
        }
    }
    // header fields the validator never checks: height_included, signature
    {
        let mut w2 = w.clone();
        if let ShardChunkHeader::V3(h) = &mut v2(&mut w2).chunk_header {
            h.height_included = h.height_included.wrapping_add(7);
        }
        push(&mut out, "hdr.height_included(unchecked)", claim.clone(), enc(&w2), Judge::Nearcore);
    }

    // ---- witness
    let ChunkStateWitness::V2(x) = w;
    let mut entries: Vec<(ChunkHash, ReceiptProof)> =
        x.source_receipt_proofs.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    if !entries.is_empty() {
        let i = rng.gen_range(0..entries.len());
        let mut e2 = entries.clone();
        e2.remove(i);
        push(&mut out, "w.drop_proof", claim.clone(), encode_with_entries(w, &e2), Judge::Nearcore);
        if let Some(bad) = corrupt_proof(&entries[i].1) {
            let mut e3 = entries.clone();
            e3[i].1 = bad.clone();
            push(&mut out, "w.corrupt_proof", claim.clone(), encode_with_entries(w, &e3), Judge::Nearcore);
            // duplicate key: bad first, good last -> last wins -> accepted
            let mut e4 = entries.clone();
            e4.insert(0, (entries[i].0.clone(), bad.clone()));
            push(&mut out, "w.dup_key_last_good", claim.clone(), encode_with_entries(w, &e4), Judge::Nearcore);
            let mut e5 = entries.clone();
            e5.push((entries[i].0.clone(), bad));
            push(&mut out, "w.dup_key_last_bad", claim.clone(), encode_with_entries(w, &e5), Judge::Nearcore);
        }
        let mut e6 = entries.clone();
        e6.reverse();
        push(&mut out, "w.unsorted_keys", claim.clone(), encode_with_entries(w, &e6), Judge::Nearcore);
        let mut e7 = entries.clone();
        e7.push((ChunkHash(CryptoHash([0xab; 32])), entries[i].1.clone()));
        push(&mut out, "w.extra_proof", claim.clone(), encode_with_entries(w, &e7), Judge::Nearcore);
    }
    {
        let mut w2 = w.clone();
        let PartialState::TrieValues(vals) = &mut v2(&mut w2).main_state_transition.base_state;
        if !vals.is_empty() {
            let i = rng.gen_range(0..vals.len());
            vals.remove(i);
            push(&mut out, "w.base_state.drop_node", claim.clone(), enc(&w2), Judge::Nearcore);
        }
    }
    {
        let mut w2 = w.clone();
        let PartialState::TrieValues(vals) = &mut v2(&mut w2).main_state_transition.base_state;
        let junk: Vec<u8> = (0..rng.gen_range(1..200)).map(|_| rng.r#gen()).collect();
        vals.push(junk.into());
        push(&mut out, "w.base_state.extra_junk", claim.clone(), enc(&w2), Judge::Nearcore);
    }
    {
        let mut w2 = w.clone();
        v2(&mut w2).main_state_transition.post_state_root.0[0] ^= 1;
        push(&mut out, "w.main_post_root", claim.clone(), enc(&w2), Judge::Nearcore);
        let mut w3 = w.clone();
        v2(&mut w3).main_state_transition.block_hash.0[0] ^= 1;
        push(&mut out, "w.main_block_hash(unchecked)", claim.clone(), enc(&w3), Judge::Nearcore);
        let mut w4 = w.clone();
        v2(&mut w4).applied_receipts_hash.0[0] ^= 1;
        push(&mut out, "w.applied_receipts_hash", claim.clone(), enc(&w4), Judge::Nearcore);
        let mut w5 = w.clone();
        v2(&mut w5).epoch_id.0.0[0] ^= 1;
        let mut c5 = claim.clone();
        c5.epoch_id = v2(&mut w5).epoch_id.0.0;
        push(&mut out, "w.epoch_id", c5, enc(&w5), Judge::Nearcore);
        let mut b6 = enc(w);
        b6.push(0);
        push(&mut out, "w.trailing_byte", claim.clone(), b6, Judge::Nearcore);
    }
    if !x.implicit_transitions.is_empty() {
        let k = rng.gen_range(0..x.implicit_transitions.len());
        let mut w2 = w.clone();
        v2(&mut w2).implicit_transitions.remove(k);
        push(&mut out, "w.implicit.drop", claim.clone(), enc(&w2), Judge::Nearcore);
        let mut w3 = w.clone();
        v2(&mut w3).implicit_transitions[k].post_state_root.0[0] ^= 1;
        push(&mut out, "w.implicit.post_root", claim.clone(), enc(&w3), Judge::Nearcore);
        let mut w4 = w.clone();
        let PartialState::TrieValues(vals) = &mut v2(&mut w4).implicit_transitions[k].base_state;
        if !vals.is_empty() {
            vals.clear();
            push(&mut out, "w.implicit.empty_base", claim.clone(), enc(&w4), Judge::Nearcore);
        }
    }

    // ---- claim context (hash-authenticated): false by the format
    let wb = enc(w);
    {
        let mut c = claim.clone();
        let i = rng.gen_range(0..c.blocks.len());
        let l = c.blocks[i].inner_rest.len();
        c.blocks[i].inner_rest[l - 1] ^= 1;
        push(&mut out, "c.inner_rest_flip", c, wb.clone(), Judge::Claim);
        let mut c = claim.clone();
        let i = rng.gen_range(0..c.blocks.len());
        let j = rng.gen_range(0..c.blocks[i].slots.len());
        c.blocks[i].slots[j].height_included ^= 1;
        push(&mut out, "c.slot_height_flip", c, wb.clone(), Judge::Claim);
        let mut c = claim.clone();
        let j = rng.gen_range(0..c.blocks[0].slots.len());
        let l = c.blocks[0].slots[j].inner.len();
        c.blocks[0].slots[j].inner[l - 50] ^= 1;
        push(&mut out, "c.slot_inner_flip", c, wb.clone(), Judge::Claim);
        if claim.blocks.len() > 1 {
            let mut c = claim.clone();
            c.blocks.pop();
            c.epoch_start_after.pop();
            push(&mut out, "c.drop_last_block", c, wb.clone(), Judge::Claim);
        }
        if let Some(p) = parent_of_last {
            let mut c = claim.clone();
            c.blocks.push(p);
            c.epoch_start_after.push(0);
            push(&mut out, "c.extra_block", c, wb.clone(), Judge::Claim);
        }
        let mut c = claim.clone();
        c.epoch_start_after[0] ^= 1;
        push(&mut out, "c.epoch_start_flip", c, wb.clone(), Judge::Claim);
    }
    // ---- trusted facts
    {
        let mut c = claim.clone();
        let (d, t) = if c.rs_total_parts == 2 { (1u16, 3u16) } else { (1, 2) };
        c.rs_data_parts = d;
        c.rs_total_parts = t;
        push(&mut out, "t.rs_params", c, wb.clone(), Judge::Nearcore);
        let mut c = claim.clone();
        c.chain_id = "other-chain".into();
        push(&mut out, "t.chain_id(unused_in_D0)", c, wb.clone(), Judge::Nearcore);
        if !claim.apply_facts.is_empty() {
            let mut c = claim.clone();
            c.apply_facts[0].minimum_stake ^= 1;
            push(&mut out, "t.minimum_stake(unused_in_D0)", c, wb.clone(), Judge::Nearcore);
        }
    }
    out
}

/// Read-set faithfulness: drop each recorded trie value of the main and of every
/// implicit transition, one at a time (capped). nearcore rejects iff it reads the
/// dropped node or value (MissingTrieValue); the Lean/Python relations must agree.
pub fn drop_each_node(claim: &Claim, w: &ChunkStateWitness, cap: usize) -> Vec<Mutant> {
    let mut out = Vec::new();
    let ChunkStateWitness::V2(x) = w;
    let PartialState::TrieValues(main) = &x.main_state_transition.base_state;
    for i in 0..main.len().min(cap) {
        let mut w2 = w.clone();
        let PartialState::TrieValues(v) = &mut v2(&mut w2).main_state_transition.base_state;
        v.remove(i);
        out.push(Mutant { name: format!("w.drop_node.main.{i}"), claim: claim.clone(), witness: borsh::to_vec(&w2).unwrap(), judge: Judge::Nearcore });
    }
    for (k, t) in x.implicit_transitions.iter().enumerate() {
        let PartialState::TrieValues(vals) = &t.base_state;
        for i in 0..vals.len().min(cap) {
            let mut w2 = w.clone();
            let PartialState::TrieValues(v) = &mut v2(&mut w2).implicit_transitions[k].base_state;
            v.remove(i);
            out.push(Mutant { name: format!("w.drop_node.implicit{k}.{i}"), claim: claim.clone(), witness: borsh::to_vec(&w2).unwrap(), judge: Judge::Nearcore });
        }
    }
    out
}
