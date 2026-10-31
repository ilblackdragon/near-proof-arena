//! Opt-in (`NEAR_L0_ROW_MUTANTS=1`) witness + claim mutants for Gate-B L0 row validation
//! (`docs/evidence/lean-chunk-completion/l0-row-validation/README.md`, third pass). Each one
//! changes the witness and the claim together, so that one d2-core guard of the successor checker
//! is the first check that fails; every one is judged by the cold validator like the other witness
//! mutants (`Judge::Nearcore`). With the variable unset nothing here runs and no RNG is consumed,
//! so every other case and mutant of a run is unchanged.
//!
//! * `l0.w.new_tx.oversize_rehashed` (row `L0-D2-020`): one more new transaction, a FunctionCall
//!   whose borsh size is `max_transaction_size + 1`, with the endorsed header re-hashed in both
//!   the claim and the witness (tx_root, encoded merkle root and length; as d1.rs
//!   `w.new_tx.*_rehashed`). nearcore's `pre_validate_chunk_state_witness` runs
//!   `check_valid_for_config` on every new transaction (`chunk_validation.rs:323-338`).
//! * `l0.w.new_tx.maxsize_rehashed`: the same at exactly `max_transaction_size` (the boundary).
//! * `l0.c.prev_block_hi_above` (row `L0-D2-025`) and `l0.c.prev_block_extra_slot` /
//!   `l0.c.prev_block_drop_slot` (row `L0-D2-023`): a fabricated previous block. One chunk slot of
//!   the segment's first block (the witness's prev block) gets `height_included = height + 1`, or
//!   one more slot (a copy of the last), or one fewer; its `chunk_headers_root` is recomputed, so
//!   the block hash changes, and the chunk header's `prev_block_hash` is rewritten to that hash in
//!   both the claim and the witness (with the witness transitions' `block_hash` where it named the
//!   old block). Every earlier check of the successor checker (decoding, hash links, start of the
//!   segment) still passes; nearcore's validator does not have that block.
use crate::enc::{Claim, block_hash};
use crate::mutate::{Judge, Mutant};
use near_client::Client;
use near_crypto::{KeyType, PublicKey, Signature};
use near_primitives::action::{Action, FunctionCallAction};
use near_primitives::hash::{CryptoHash, hash};
use near_primitives::merkle::{combine_hash, merklize};
use near_primitives::sharding::{
    ChunkHash, ChunkHashHeight, EncodedShardChunkBody, ShardChunkHeader, TransactionReceipt,
};
use near_primitives::stateless_validation::state_witness::{ChunkStateWitness, ChunkStateWitnessV2};
use near_primitives::transaction::{SignedTransaction, Transaction, TransactionV0};
use near_primitives::types::{Balance, Gas};
use reed_solomon_erasure::galois_8::ReedSolomon;

/// `max_transaction_size` at PV86 (`TxD1.lean` `maxTransactionSize`, nearcore parameters).
const MAX_TX_SIZE: usize = 1_572_864;

pub fn enabled() -> bool {
    std::env::var_os("NEAR_L0_ROW_MUTANTS").is_some()
}

fn v2(w: &mut ChunkStateWitness) -> &mut ChunkStateWitnessV2 {
    match w {
        ChunkStateWitness::V2(b) => b,
    }
}

/// The witness with its chunk header's inner replaced (d1.rs `with_inner`).
fn with_inner(w: &ChunkStateWitness, inner: &[u8]) -> Option<ChunkStateWitness> {
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

/// A FunctionCall transaction whose borsh (wire) size is exactly `size`.
fn sized_tx(size: usize) -> Option<SignedTransaction> {
    let mk = |n: usize| {
        let tx = Transaction::V0(TransactionV0 {
            signer_id: "l0-size.near".parse().unwrap(),
            public_key: PublicKey::empty(KeyType::ED25519),
            nonce: 1,
            receiver_id: "l0-size.near".parse().unwrap(),
            block_hash: CryptoHash::default(),
            actions: vec![Action::FunctionCall(Box::new(FunctionCallAction {
                method_name: "m".into(),
                args: vec![0u8; n],
                gas: Gas::from_teragas(1),
                deposit: Balance::ZERO,
            }))],
        });
        SignedTransaction::new(Signature::empty(KeyType::ED25519), tx)
    };
    let s0 = borsh::to_vec(&mk(0)).ok()?.len();
    let t = mk(size.checked_sub(s0)?);
    (borsh::to_vec(&t).ok()?.len() == size).then_some(t)
}

/// The slot leaves' merkle root (`Block::compute_chunk_headers_root`: chunk hash and height).
fn headers_root(slots: &[crate::enc::ChunkSlot]) -> Option<CryptoHash> {
    let mut leaves = Vec::new();
    for s in slots {
        let emr: [u8; 32] = s.inner.get(97..129)?.try_into().ok()?;
        leaves.push(ChunkHashHeight(ChunkHash(combine_hash(&hash(&s.inner), &CryptoHash(emr))), s.height_included));
    }
    Some(merklize(&leaves).0)
}

pub fn mutants(client: &Client, claim: &Claim, w: &ChunkStateWitness) -> Vec<Mutant> {
    let mut out = Vec::new();
    let push = |out: &mut Vec<Mutant>, name: &str, claim: Claim, w: &ChunkStateWitness| {
        out.push(Mutant { name: name.into(), claim, witness: borsh::to_vec(w).unwrap(), judge: Judge::Nearcore })
    };
    let ChunkStateWitness::V2(x) = w;
    // L0-D2-020: one more, oversized, new transaction (header re-hashed)
    if let Ok(chunk) = client.chain.get_chunk(w.chunk_header().chunk_hash()) {
        let receipts = chunk.prev_outgoing_receipts().to_vec();
        let d = client.epoch_manager.num_data_parts();
        let total = client.epoch_manager.num_total_parts();
        let rs = ReedSolomon::new(d, total - d).unwrap();
        let rehash = |txs: Vec<SignedTransaction>| -> Option<(Claim, ChunkStateWitness)> {
            let (parts, len) = near_primitives::reed_solomon::reed_solomon_encode(&rs, &TransactionReceipt(txs.clone(), receipts.clone()));
            let body = EncodedShardChunkBody { parts };
            let (emr, _) = body.get_merkle_hash_and_paths();
            let mut inner = claim.chunk_inner.clone();
            inner[97..129].copy_from_slice(&emr.0);
            inner[129..137].copy_from_slice(&(len as u64).to_le_bytes());
            inner[217..249].copy_from_slice(&merklize(&txs).0.0);
            let mut w2 = with_inner(w, &inner)?;
            v2(&mut w2).new_transactions = txs;
            let mut c = claim.clone();
            c.chunk_inner = inner;
            Some((c, w2))
        };
        for (name, size) in [("l0.w.new_tx.oversize_rehashed", MAX_TX_SIZE + 1), ("l0.w.new_tx.maxsize_rehashed", MAX_TX_SIZE)] {
            if let Some(t) = sized_tx(size) {
                let mut txs = x.new_transactions.clone();
                txs.push(t);
                if let Some((c, w2)) = rehash(txs) {
                    push(&mut out, name, c, &w2);
                }
            }
        }
    }
    // L0-D2-023 / L0-D2-025: a fabricated prev block (the segment's first block)
    let Some(b0) = claim.blocks.first() else { return out };
    if headers_root(&b0.slots).map(|r| r.0.to_vec()) != b0.inner_rest.get(64..96).map(|s| s.to_vec()) {
        return out; // unexpected header layout: emit nothing
    }
    let old = block_hash(b0);
    let height = match b0.inner_lite.get(0..8) {
        Some(h) => u64::from_le_bytes(h.try_into().unwrap()),
        None => return out,
    };
    let own = claim.chunk_inner.get(145..153).map(|s| u64::from_le_bytes(s.try_into().unwrap()));
    let shard_of = |s: &crate::enc::ChunkSlot| s.inner.get(145..153).map(|v| u64::from_le_bytes(v.try_into().unwrap()));
    let refab = |f: &dyn Fn(&mut crate::enc::BlockRec) -> bool| -> Option<(Claim, ChunkStateWitness)> {
        let mut c = claim.clone();
        if !f(&mut c.blocks[0]) {
            return None;
        }
        let root = headers_root(&c.blocks[0].slots)?;
        c.blocks[0].inner_rest[64..96].copy_from_slice(&root.0);
        let new = block_hash(&c.blocks[0]);
        c.chunk_inner[1..33].copy_from_slice(&new);
        let mut w2 = with_inner(w, &c.chunk_inner)?;
        let x2 = v2(&mut w2);
        if x2.main_state_transition.block_hash == CryptoHash(old) {
            x2.main_state_transition.block_hash = CryptoHash(new);
        }
        for t in x2.implicit_transitions.iter_mut() {
            if t.block_hash == CryptoHash(old) {
                t.block_hash = CryptoHash(new);
            }
        }
        Some((c, w2))
    };
    // another shard's slot: a new chunk there (missed count stays 0), else any other slot
    let pick = |b: &crate::enc::BlockRec| -> Option<usize> {
        let other = |s: &crate::enc::ChunkSlot| own.is_some() && shard_of(s) != own;
        b.slots.iter().position(|s| other(s) && s.height_included == height)
            .or_else(|| b.slots.iter().position(other))
    };
    if let Some((c, w2)) = refab(&|b| match pick(b) {
        Some(j) => {
            b.slots[j].height_included = height + 1;
            true
        }
        None => false,
    }) {
        push(&mut out, "l0.c.prev_block_hi_above", c, &w2);
    }
    if let Some((c, w2)) = refab(&|b| match b.slots.last().cloned() {
        Some(s) => {
            b.slots.push(s);
            true
        }
        None => false,
    }) {
        push(&mut out, "l0.c.prev_block_extra_slot", c, &w2);
    }
    if let Some((c, w2)) = refab(&|b| match b.slots.last() {
        Some(s) if b.slots.len() > 1 && own.is_some() && shard_of(s) != own => {
            b.slots.pop();
            true
        }
        _ => false,
    }) {
        push(&mut out, "l0.c.prev_block_drop_slot", c, &w2);
    }
    out
}
