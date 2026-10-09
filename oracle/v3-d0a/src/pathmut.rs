//! `w.path_depth` (A10, bound D_p = 32) mutants for domain D0a.
//!
//! Construction (modelled on src/a2mut.rs `foreign_routing`; on an honest, nearcore-accepted
//! D0a case whose segment starts at B2 = `blocks[0]`, no implicit transitions): pick the first
//! new source chunk of B2 (slot order) whose proof is in the witness; append deterministic
//! synthetic items to its Merkle path (`ReceiptProof.1.proof`) up to exactly `depth` items
//! (sibling = sha256(TAG ‖ i as u64 LE), direction Left for even absolute index i, Right for
//! odd); recompute that chunk's `prev_outgoing_receipts_root` with nearcore
//! `compute_root_from_path` over the extended path, its chunk hash (the proof key), B2's
//! `chunk_headers_root` and hash, and the endorsed chunk's `prev_block_hash` (claim and
//! witness header); re-key the proof entry. The receipts, the applied receipts, the
//! scheduler inputs (B2's congestion info and bandwidth requests, and its *prev* hash, the RNG
//! seed) and every state root are unchanged, so `Rel` holds by construction.
//!
//! Unlike the A2/A8 mutants, these are judged by nearcore's own validator: `inject` writes the
//! mutated B2 (a nearcore `Block` rebuilt with the test-utils mutators, whose recomputed hash
//! must equal the claim-side hash) and its `BlockInfo` (B2's, re-keyed) into the judging
//! client's store, so `pre_validate_chunk_state_witness` / `validate_chunk_state_witness`
//! find the endorsed chunk's prev block. The written keys are fresh hashes no canonical block
//! references (insert-only columns; an identical re-insert is a no-op).

use crate::a2mut::with_header_inner;
use crate::enc::{Claim, sha256};
use crate::mutate::encode_with_entries;
use near_client::Client;
use near_primitives::block::Block;
use near_primitives::hash::CryptoHash;
use near_primitives::merkle::{Direction, MerklePathItem, compute_root_from_path, merklize};
use near_primitives::sharding::{ChunkHash, ReceiptList, ReceiptProof, ShardChunkHeader};
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;

pub const TAG: &[u8] = b"near-arena/v3-d0a/w.path_depth/synthetic-sibling";

pub struct PathMutant {
    pub name: String,
    pub claim: Claim,
    /// nearcore borsh of the mutated `ChunkStateWitness`.
    pub witness: Vec<u8>,
    /// The mutated B2 as a nearcore block (for `inject`).
    pub block: Block,
    /// Slot index of the mutated source chunk.
    pub slot: usize,
}

fn chunk_hash(inner: &[u8]) -> [u8; 32] {
    let mut v = sha256(inner).to_vec();
    v.extend_from_slice(&inner[97..129]);
    sha256(&v)
}

/// The synthetic path item at absolute index `i`.
pub fn synthetic_item(i: usize) -> MerklePathItem {
    let mut b = TAG.to_vec();
    b.extend((i as u64).to_le_bytes());
    MerklePathItem {
        hash: CryptoHash(sha256(&b)),
        direction: if i.is_multiple_of(2) {
            Direction::Left
        } else {
            Direction::Right
        },
    }
}

/// Mutant with the chosen proof's path extended to exactly `depth` items (None if no new
/// source chunk of B2 has its proof in the witness, or its path is already longer).
pub fn extend_path(
    claim: &Claim,
    w: &ChunkStateWitness,
    b2: &Block,
    depth: usize,
    name: &str,
) -> Option<PathMutant> {
    let ChunkStateWitness::V2(x) = w;
    let rec = &claim.blocks[0];
    let height = u64::from_le_bytes(rec.inner_lite[0..8].try_into().ok()?);
    for (j, slot) in rec.slots.iter().enumerate() {
        if slot.height_included != height {
            continue;
        }
        let key = chunk_hash(&slot.inner);
        let Some((k, proof)) = x.source_receipt_proofs.iter().find(|(k, _)| k.0.0 == key) else {
            continue;
        };
        let n0 = proof.1.proof.len();
        if n0 > depth {
            continue;
        }
        let mut sp = proof.1.clone();
        sp.proof.extend((n0..depth).map(synthetic_item));
        let item = CryptoHash::hash_borsh(ReceiptList(proof.1.to_shard_id, &proof.0));
        let leaf = CryptoHash::hash_borsh(item);
        // the original path must reproduce the slot's root (sanity of the byte offsets)
        if compute_root_from_path(&proof.1.proof, leaf).0[..] != slot.inner[185..217] {
            return None;
        }
        let root = compute_root_from_path(&sp.proof, leaf);
        let mut c = claim.clone();
        c.blocks[0].slots[j].inner[185..217].copy_from_slice(&root.0);
        let leaves: Vec<([u8; 32], u64)> = c.blocks[0]
            .slots
            .iter()
            .map(|s| (chunk_hash(&s.inner), s.height_included))
            .collect();
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
            .map(|(kk, v)| {
                if kk == k {
                    (new_key.clone(), ReceiptProof(v.0.clone(), sp.clone()))
                } else {
                    (kk.clone(), v.clone())
                }
            })
            .collect();
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        // the same B2 as a nearcore block
        let mut blk = b2.clone();
        let mut chunks: Vec<ShardChunkHeader> = blk.chunks().iter_raw().cloned().collect();
        let ShardChunkHeader::V3(h) = &chunks[j] else {
            return None;
        };
        let mut hb = vec![2u8];
        hb.extend_from_slice(&c.blocks[0].slots[j].inner);
        hb.extend(h.height_included.to_le_bytes());
        hb.extend(borsh::to_vec(&h.signature).ok()?);
        let nh: ShardChunkHeader = borsh::from_slice(&hb).ok()?;
        if nh.chunk_hash().0 != new_key.0 {
            return None;
        }
        chunks[j] = nh;
        blk.set_chunks(chunks);
        blk.mut_header().set_chunk_headers_root(chr);
        blk.mut_header().init();
        if blk.hash().0 != bh {
            eprintln!("pathmut: nearcore block hash differs from the claim-side hash");
            return None;
        }
        return Some(PathMutant {
            name: name.into(),
            claim: c,
            witness: encode_with_entries(&w2, &entries),
            block: blk,
            slot: j,
        });
    }
    None
}

/// Make the mutated B2 known to `client` (chain store: Block + BlockHeader; epoch manager:
/// B2's BlockInfo re-keyed), so nearcore's validator can judge the mutant.
pub fn inject(client: &Client, orig: &CryptoHash, blk: &Block) -> Result<(), String> {
    use near_chain::ChainStoreAccess;
    use near_primitives::epoch_block_info::BlockInfo;
    use near_store::DBCol;
    let mut info: BlockInfo = (*client
        .epoch_manager
        .get_block_info(orig)
        .map_err(|e| e.to_string())?)
    .clone();
    let h = *blk.hash();
    match &mut info {
        BlockInfo::V1(i) => i.hash = h,
        BlockInfo::V2(i) => i.hash = h,
        BlockInfo::V3(i) => i.hash = h,
        BlockInfo::V4(i) => i.hash = h,
        BlockInfo::V5(i) => i.hash = h,
    }
    let store = client.chain.chain_store().store();
    let mut u = store.store_update();
    u.insert_ser(DBCol::Block, h.as_ref(), blk);
    u.insert_ser(DBCol::BlockHeader, h.as_ref(), blk.header());
    u.insert_ser(DBCol::BlockInfo, h.as_ref(), &info);
    u.commit();
    Ok(())
}

/// Longest Merkle path over the witness's source receipt proofs (0 if none).
pub fn max_path_depth(w: &ChunkStateWitness) -> u64 {
    let ChunkStateWitness::V2(x) = w;
    x.source_receipt_proofs
        .values()
        .map(|p| p.1.proof.len() as u64)
        .max()
        .unwrap_or(0)
}
