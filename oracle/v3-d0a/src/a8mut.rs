//! A8 (`c.bw_requests`) mutant for domain D0a (spec/near-chunk-validation-v0a.md §2.3a).
//!
//! Construction (on an honest, nearcore-accepted D0a case whose segment starts at B2, i.e.
//! `blocks[0]` holds the shard's last new chunk and there are no implicit transitions):
//! pick a slot `j` of `blocks[0]` other than the validated shard's (an old slot, i.e. one not
//! holding a new chunk, if there is one, so no source-proof key changes), decode its
//! `ShardChunkHeaderInner` with nearcore borsh and give its `BandwidthRequests` a repeated
//! `to_shard`: if it already has a request `(t, bitmap)`, append `(t, 0)`; otherwise append
//! `(t, 0), (t, 0)` with `t` the first shard id of the layout. Then re-hash as the A2 mutant:
//! the slot's chunk hash (and, for a new slot, its source-proof key), `blocks[0]`'s
//! `chunk_headers_root` and hash, and the endorsed chunk's `prev_block_hash` (claim and
//! witness header).
//!
//! Why `Rel` (and `RelD0`) still hold: the only reader of a slot's bandwidth requests is the
//! bandwidth scheduler run for B2 (and for each implicit block, none here). nearcore converts
//! each request with `SchedulerBandwidthRequest::new`
//! (runtime/runtime/src/bandwidth_scheduler/scheduler.rs:610-640), which returns `None` (the
//! request is ignored, before any shuffle / RNG use) when no bit of the bitmap yields an
//! increase above the base bandwidth -- always the case for the all-zero bitmap. So the
//! grants, the scheduler state written to `0x0f`, the applied receipts and every root are
//! unchanged; the slot's other fields (congestion info, height_included, outgoing-receipts
//! root) are unchanged; everything hashed is recomputed. The case violates exactly A8.

use crate::a2mut::with_header_inner;
use crate::enc::{Claim, sha256};
use crate::mutate::encode_with_entries;
use near_primitives::bandwidth_scheduler::{BandwidthRequest, BandwidthRequestBitmap, BandwidthRequests};
use near_primitives::hash::CryptoHash;
use near_primitives::sharding::shard_chunk_header_inner::ShardChunkHeaderInner;
use near_primitives::sharding::{ChunkHash, ReceiptProof};
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;

pub struct A8Mutant {
    pub name: String,
    pub claim: Claim,
    pub witness: Vec<u8>,
}

fn chunk_hash(inner: &[u8]) -> [u8; 32] {
    let mut v = sha256(inner).to_vec();
    v.extend_from_slice(&inner[97..129]);
    sha256(&v)
}

/// The slot inner with a repeated `to_shard` (None if it is not a V4/V5 inner or does not
/// round-trip through nearcore borsh).
fn dup_inner(raw: &[u8], default_to: u16) -> Option<Vec<u8>> {
    let mut inner: ShardChunkHeaderInner = borsh::from_slice(raw).ok()?;
    if borsh::to_vec(&inner).ok()? != raw {
        return None;
    }
    let reqs = match &mut inner {
        ShardChunkHeaderInner::V4(x) => &mut x.bandwidth_requests,
        ShardChunkHeaderInner::V5(x) => &mut x.bandwidth_requests,
        _ => return None,
    };
    let BandwidthRequests::V1(r) = reqs;
    let zero = |t: u16| BandwidthRequest { to_shard: t, requested_values_bitmap: BandwidthRequestBitmap::new() };
    match r.requests.first().map(|q| q.to_shard) {
        Some(t) => r.requests.push(zero(t)),
        None => {
            r.requests.push(zero(default_to));
            r.requests.push(zero(default_to));
        }
    }
    borsh::to_vec(&inner).ok()
}

pub fn dup_bw_request(
    claim: &Claim,
    w: &ChunkStateWitness,
    layout: &near_primitives::shard_layout::ShardLayout,
    own: near_primitives::types::ShardId,
) -> Option<A8Mutant> {
    use near_primitives::merkle::merklize;
    let ChunkStateWitness::V2(x) = w;
    let b0 = &claim.blocks[0];
    let height = u64::from_le_bytes(b0.inner_lite[0..8].try_into().ok()?);
    let own_idx = layout.get_shard_index(own).ok()?;
    let default_to: u16 = layout.shard_ids().next()?.into();
    // old (non-new) slots first, then new ones; never the validated shard's slot
    let mut order: Vec<usize> = (0..b0.slots.len()).filter(|&j| j != own_idx).collect();
    order.sort_by_key(|&j| b0.slots[j].height_included == height);
    let j = *order.first()?;
    let old_key = chunk_hash(&b0.slots[j].inner);
    let new_inner = dup_inner(&b0.slots[j].inner, default_to)?;
    let mut c = claim.clone();
    c.blocks[0].slots[j].inner = new_inner;
    let new_key = chunk_hash(&c.blocks[0].slots[j].inner);
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
    // a new slot's source proof is keyed by its chunk hash: re-key it
    let is_new = b0.slots[j].height_included == height;
    let mut entries: Vec<(ChunkHash, ReceiptProof)> = x
        .source_receipt_proofs
        .iter()
        .map(|(k, v)| {
            if is_new && k.0.0 == old_key {
                (ChunkHash(CryptoHash(new_key)), v.clone())
            } else {
                (k.clone(), v.clone())
            }
        })
        .collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    Some(A8Mutant { name: "c.dup_bw_request".into(), claim: c, witness: encode_with_entries(&w2, &entries) })
}
