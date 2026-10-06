//! Re-execution of the transfer batch (`NearSpec.TransferV1.runBatch`) and
//! the honest prover.

use super::spec::*;
use super::trie::{nibbles_of, PTrie, Slot, Store};
use super::wire::Writer;
use super::sha256;
use sha2::Sha256;
use sha2::Digest;

const U128_MAX: u128 = u128::MAX;

pub struct Outputs {
    pub slice_post_root: [u8; 32],
    pub outcome_root: [u8; 32],
    pub refund_count: u32,
    pub refunds_commitment: [u8; 32],
    pub gas_burnt_total: u64,
    pub tokens_burnt_total: u128,
}

/// `DomainStatic` minus the trie-root equality (checked by the caller).
pub fn domain_static(
    protocol_version: u32,
    chain_id: &[u8],
    gas_limit: u64,
    receipts: &[Receipt<'_>],
    revealed_bytes: u64,
) -> Result<(), String> {
    if protocol_version != PROTOCOL_VERSION {
        return Err("out of domain: protocol_version".into());
    }
    if chain_id != CHAIN_ID {
        return Err("out of domain: chain_id".into());
    }
    let n = receipts.len();
    if n < 1 || n > MAX_BATCH {
        return Err("out of domain: batch size".into());
    }
    if (n as u128 - 1) * G as u128 >= gas_limit as u128 {
        return Err("out of domain: gas limit".into());
    }
    if !receipts.iter().all(receipt_in_slice) {
        return Err("out of domain: receipt fields".into());
    }
    let mut ids: Vec<&[u8; 32]> = receipts.iter().map(|r| &r.receipt_id).collect();
    ids.sort_unstable();
    if ids.windows(2).any(|p| p[0] == p[1]) {
        return Err("out of domain: duplicate receipt id".into());
    }
    if revealed_bytes > MAX_WITNESS_BYTES {
        return Err("out of domain: witness too large".into());
    }
    Ok(())
}

/// nearcore `merklize` root over leaves (`NearSpec.merkleRoot`).
pub fn merkle_root(mut level: Vec<[u8; 32]>) -> [u8; 32] {
    if level.is_empty() {
        return [0; 32];
    }
    let mut buf = [0u8; 64];
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len().div_ceil(2));
        for p in level.chunks(2) {
            if p.len() == 2 {
                buf[..32].copy_from_slice(&p[0]);
                buf[32..].copy_from_slice(&p[1]);
                next.push(sha256(&buf));
            } else {
                next.push(p[0]);
            }
        }
        level = next;
    }
    level[0]
}

/// `applyAll` over the batch; mutates `trie` in place. `Err` = out of domain.
pub fn run_batch(
    block_height: u64,
    block_gas_price: u128,
    trie: &mut PTrie<'_>,
    receipts: &[Receipt<'_>],
) -> Result<Outputs, String> {
    let mut leaves = Vec::with_capacity(receipts.len());
    let mut refunds = Writer::with_capacity(4 + 200 * receipts.len());
    refunds.u32(0); // patched below
    let mut refund_count = 0u32;
    let mut tokens: u128 = 0;
    let mut path = Vec::with_capacity(64);
    let mut partial = Writer::with_capacity(256);
    for (idx, r) in receipts.iter().enumerate() {
        let fail = || format!("out of domain: receipt {idx} (missing/unrevealed receiver, not AccountV1, overflow, or storage stake)");
        let key = nibbles_of(0, r.receiver);
        path.clear();
        let owner = trie.locate(&key, &mut path).ok_or_else(fail)?;
        let raw = trie.slot(owner).current().ok_or_else(fail)?;
        if raw.len() != 72 {
            return Err(fail());
        }
        let amount = u128::from_le_bytes(raw[0..16].try_into().unwrap());
        if amount == U128_MAX {
            return Err(fail());
        }
        let locked = u128::from_le_bytes(raw[16..32].try_into().unwrap());
        let storage = u64::from_le_bytes(raw[64..72].try_into().unwrap());
        let amount2 = amount.checked_add(r.deposit).filter(|&a| a < U128_MAX).ok_or_else(fail)?;
        let total = amount2.checked_add(locked).ok_or_else(fail)?;
        if !(total >= STORAGE_AMOUNT_PER_BYTE * storage as u128 || storage <= ZERO_BALANCE_STORAGE_LIMIT) {
            return Err(fail());
        }
        let p = r.gas_price.min(block_gas_price);
        let burnt = (G as u128).checked_mul(p).ok_or_else(fail)?;
        let surplus = (G as u128).checked_mul(r.gas_price - p).ok_or_else(fail)?;
        tokens = tokens.checked_add(burnt).ok_or_else(fail)?;
        // write the new account value
        let mut nv: Box<[u8]> = raw.into();
        nv[0..16].copy_from_slice(&amount2.to_le_bytes());
        match trie.slot_mut(owner) {
            Slot::Val { cur, .. } => *cur = Some(nv),
            Slot::Ref { .. } => unreachable!(),
        }
        for &i in &path {
            trie.nodes[i as usize].dirty = true;
        }
        // outcome (+ refund)
        partial.0.clear();
        if surplus != 0 {
            let mut idb = [0u8; 48];
            idb[..32].copy_from_slice(&r.receipt_id);
            idb[32..40].copy_from_slice(&block_height.to_le_bytes());
            let rid = sha256(&idb);
            write_refund(&mut refunds, r, &rid, surplus);
            refund_count += 1;
            partial.u32(1).raw(&rid);
        } else {
            partial.u32(0);
        }
        partial.u64(G).u128(burnt).bytes(r.receiver).u8(2).u32(0);
        let ph = sha256(&partial.0);
        let mut h = Sha256::new();
        h.update(2u32.to_le_bytes());
        h.update(r.receipt_id);
        h.update(ph);
        leaves.push(h.finalize().into());
    }
    refunds.0[0..4].copy_from_slice(&refund_count.to_le_bytes());
    Ok(Outputs {
        slice_post_root: trie.root_hash(),
        outcome_root: merkle_root(leaves),
        refund_count,
        refunds_commitment: sha256(&refunds.0),
        gas_burnt_total: G * receipts.len() as u64,
        tokens_burnt_total: tokens,
    })
}

/// The claim of a request and witness (`NearSpec.Codec.deriveClaim`), or an
/// out-of-domain error.  (Adapted from reexec-witness `engine::prove`, without
/// the proof encoding.)
pub fn derive_claim(request: &[u8], witness: &[u8]) -> Result<Claim, String> {
    let req = decode_request(request).map_err(|e| format!("request: {e}"))?;
    let (wroot, values) = decode_witness(witness).map_err(|e| format!("witness: {e}"))?;
    if wroot != req.pre_state_root {
        return Err("witness pre_state_root != request pre_state_root".into());
    }
    let mut store: Store<'_> = Store::with_capacity(values.len());
    for v in &values {
        store.insert(sha256(v), v);
    }
    let keys: Vec<Vec<u8>> = req.receipts.iter().map(|r| nibbles_of(0, r.receiver)).collect();
    let key_refs: Vec<&[u8]> = keys.iter().map(|k| k.as_slice()).collect();
    let mut trie = PTrie::build(&store, req.pre_state_root, &key_refs)?;
    domain_static(req.protocol_version, req.chain_id, req.gas_limit, &req.receipts, trie.revealed_bytes())?;
    let out = run_batch(req.block_height, req.block_gas_price, &mut trie, &req.receipts)?;
    let mut rc = Sha256::new();
    rc.update(req.shard_id.to_le_bytes());
    rc.update(req.receipts_bytes);
    Ok(Claim {
        protocol_version: req.protocol_version,
        chain_id: req.chain_id.to_vec(),
        shard_id: req.shard_id,
        block_height: req.block_height,
        block_gas_price: req.block_gas_price,
        gas_limit: req.gas_limit,
        pre_state_root: req.pre_state_root,
        receipt_count: req.receipts.len() as u32,
        receipts_commitment: rc.finalize().into(),
        slice_post_root: out.slice_post_root,
        outcome_root: out.outcome_root,
        refund_count: out.refund_count,
        refunds_commitment: out.refunds_commitment,
        gas_burnt_total: out.gas_burnt_total,
        tokens_burnt_total: out.tokens_burnt_total,
    })
}
