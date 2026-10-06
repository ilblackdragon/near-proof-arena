//! A2 (`w.proof_routing`) mutant for domain D0a (spec/near-chunk-validation-v0a.md).
//! `with_header_inner` / `v2` are copies of the private helpers of ../v3/src/mutate.rs
//! (that file is shared unmodified and pinned).

use crate::enc::Claim;
use crate::mutate::encode_with_entries;
use near_primitives::hash::CryptoHash;
use near_primitives::sharding::{ChunkHash, ReceiptProof, ShardChunkHeader};
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;

pub struct A2Mutant {
    pub name: String,
    pub claim: Claim,
    pub witness: Vec<u8>,
}

pub(crate) fn v2(w: &mut ChunkStateWitness) -> &mut near_primitives::stateless_validation::state_witness::ChunkStateWitnessV2 {
    match w {
        ChunkStateWitness::V2(b) => b,
    }
}

pub(crate) fn with_header_inner(w: &ChunkStateWitness, inner: &[u8]) -> Option<ChunkStateWitness> {
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

/// A2 (`w.proof_routing`) mutant: a foreign-routed receipt with a *valid* Merkle path.
///
/// Requires the segment to start at B2 (`blocks[0]` holds the shard's last new chunk, no
/// implicit transitions). In B2 pick a new source chunk whose proof is in the witness;
/// append a D0-shaped receipt whose receiver routes (nearcore `account_id_to_shard_id`) to
/// another shard; recompute that chunk's `prev_outgoing_receipts_root` from the proof's own
/// path, its chunk hash (the proof key), B2's `chunk_headers_root` and hash, and the
/// endorsed chunk's `prev_block_hash` (claim and witness header). Everything nearcore's
/// validator reads is then consistent, `filter_incoming_receipts_for_shard` drops the
/// foreign receipt, and the applied receipts, execution and header comparisons are
/// unchanged: `Rel` holds by construction, but the case is outside D0 (A2).
pub fn foreign_routing(
    claim: &Claim,
    w: &ChunkStateWitness,
    layout: &near_primitives::shard_layout::ShardLayout,
    own: near_primitives::types::ShardId,
) -> Option<A2Mutant> {
    use crate::enc::sha256;
    use near_primitives::merkle::{compute_root_from_path, merklize};
    use near_primitives::receipt::Receipt;
    use near_primitives::sharding::ReceiptList;
    let ChunkStateWitness::V2(x) = w;
    let b2 = &claim.blocks[0];
    let height = u64::from_le_bytes(b2.inner_lite[0..8].try_into().ok()?);
    let chunk_hash = |inner: &[u8]| -> [u8; 32] {
        let mut v = sha256(inner).to_vec();
        v.extend_from_slice(&inner[97..129]);
        sha256(&v)
    };
    // a template receipt (any receipt of any proof)
    let tmpl = x.source_receipt_proofs.values().flat_map(|p| p.0.iter()).next()?.clone();
    // a named receiver routed to another shard
    let recv: near_primitives::types::AccountId = ["aa", "zz", "mm", "near", "s0", "s9z", "test0", "zzzz.near"]
        .iter()
        .filter_map(|a| a.parse().ok())
        .find(|a| layout.account_id_to_shard_id(a) != own)?;
    let mut rb = borsh::to_vec(&tmpl).ok()?;
    // ReceiptV0 (untagged): predecessor (u32 len ‖ bytes), receiver (u32 len ‖ bytes), receipt_id
    let l1 = u32::from_le_bytes(rb[0..4].try_into().ok()?) as usize;
    let off = 4 + l1;
    let l2 = u32::from_le_bytes(rb[off..off + 4].try_into().ok()?) as usize;
    let mut nb = rb[..off].to_vec();
    nb.extend((recv.len() as u32).to_le_bytes());
    nb.extend(recv.as_bytes());
    let mut tail = rb.split_off(off + 4 + l2);
    tail[0] ^= 0x5a; // distinct receipt_id
    nb.extend(tail);
    let foreign: Receipt = borsh::from_slice(&nb).ok()?;
    for (j, slot) in b2.slots.iter().enumerate() {
        if slot.height_included != height {
            continue;
        }
        let key = chunk_hash(&slot.inner);
        let Some((k, proof)) = x.source_receipt_proofs.iter().find(|(k, _)| k.0.0 == key) else { continue };
        let mut receipts = proof.0.clone();
        receipts.push(foreign.clone());
        let item = near_primitives::hash::CryptoHash::hash_borsh(ReceiptList(proof.1.to_shard_id, &receipts));
        let root = compute_root_from_path(&proof.1.proof, near_primitives::hash::CryptoHash::hash_borsh(item));
        let mut c = claim.clone();
        c.blocks[0].slots[j].inner[185..217].copy_from_slice(&root.0);
        let leaves: Vec<([u8; 32], u64)> =
            c.blocks[0].slots.iter().map(|s| (chunk_hash(&s.inner), s.height_included)).collect();
        let (chr, _) = merklize(&leaves);
        c.blocks[0].inner_rest[64..96].copy_from_slice(&chr.0);
        let bh = {
            let mut v = sha256(&c.blocks[0].inner_lite).to_vec();
            v.extend(sha256(&c.blocks[0].inner_rest));
            let mut v2 = sha256(&v).to_vec();
            v2.extend(c.blocks[0].prev_hash);
            sha256(&v2)
        };
        c.chunk_inner[1..33].copy_from_slice(&bh);
        let w2 = with_header_inner(w, &c.chunk_inner)?;
        let new_key = ChunkHash(CryptoHash(chunk_hash(&c.blocks[0].slots[j].inner)));
        let mut entries: Vec<(ChunkHash, ReceiptProof)> = x
            .source_receipt_proofs
            .iter()
            .map(|(kk, v)| if kk == k { (new_key.clone(), ReceiptProof(receipts.clone(), v.1.clone())) } else { (kk.clone(), v.clone()) })
            .collect();
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        return Some(A2Mutant {
            name: "w.foreign_routed_receipt".into(),
            claim: c,
            witness: encode_with_entries(&w2, &entries),
        });
    }
    None
}
