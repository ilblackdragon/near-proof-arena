//! Rust re-checker (TEST ORACLE ONLY — the deployed verifier is the Lean
//! model). Decodes the claim and proof and re-executes the relation.

use crate::engine::{domain_static, run_batch};
use crate::proof::read_key;
use crate::spec::*;
use crate::trie::{Kind, Node, PTrie, Slot, NONE};
use crate::wire::{Reader, WResult, WireError};
use crate::Sha256;
use sha2::Digest;

fn read_node<'a>(r: &mut Reader<'a>, t: &mut PTrie<'a>, depth: usize) -> WResult<u32> {
    if depth > 1024 {
        return Err(WireError("trie too deep"));
    }
    let tag = r.u8("node tag")?;
    let kind = match tag {
        0 => {
            let h = r.hash("hash")?;
            t.nodes.push(Node { kind: Kind::Hash, mem: 0, hash: h, dirty: false });
            return Ok((t.nodes.len() - 1) as u32);
        }
        1 | 2 => {
            let key = read_key(r)?;
            let slot = if tag == 1 {
                Slot::Val { orig: r.bytes("value")?, cur: None }
            } else {
                Slot::Ref { len: r.u32("len")?, hash: r.hash("hash")? }
            };
            Kind::Leaf { key, slot }
        }
        3 => {
            let key = read_key(r)?;
            let child = read_node(r, t, depth + 1)?;
            Kind::Ext { key, child }
        }
        4..=6 => {
            let value = match tag {
                4 => None,
                5 => Some(Slot::Val { orig: r.bytes("value")?, cur: None }),
                _ => Some(Slot::Ref { len: r.u32("len")?, hash: r.hash("hash")? }),
            };
            let bm = r.u16("bitmap")?;
            let mut kids = [NONE; 16];
            for (i, k) in kids.iter_mut().enumerate() {
                if bm >> i & 1 == 1 {
                    *k = read_node(r, t, depth + 1)?;
                }
            }
            Kind::Branch { value, kids }
        }
        _ => return Err(WireError("node tag")),
    };
    let mem = r.u64("mem")?;
    t.nodes.push(Node { kind, mem, hash: [0; 32], dirty: true });
    Ok((t.nodes.len() - 1) as u32)
}

/// `true` iff the proof establishes the claim.
pub fn verify(claim: &[u8], proof: &[u8]) -> bool {
    verify_explain(claim, proof).is_ok()
}

pub fn verify_explain(claim: &[u8], proof: &[u8]) -> Result<(), String> {
    let c = Claim::decode(claim).map_err(|e| format!("claim: {e}"))?;
    let mut r = Reader::new(proof);
    let n = r.u32("receipt count").map_err(|e| e.to_string())? as usize;
    let mut receipts = Vec::with_capacity(n.min(MAX_BATCH));
    for _ in 0..n {
        receipts.push(read_receipt(&mut r).map_err(|e| e.to_string())?);
    }
    let receipts_bytes = &proof[..r.pos];
    let mut t = PTrie { nodes: Vec::new(), root: 0 };
    t.root = read_node(&mut r, &mut t, 0).map_err(|e| e.to_string())?;
    r.finish().map_err(|e| e.to_string())?;
    if receipts.len() as u64 != c.receipt_count as u64 {
        return Err("receipt count".into());
    }
    domain_static(c.protocol_version, &c.chain_id, c.gas_limit, &receipts, t.revealed_bytes())?;
    let mut h = Sha256::new();
    h.update(c.shard_id.to_le_bytes());
    h.update(receipts_bytes);
    if <[u8; 32]>::from(h.finalize()) != c.receipts_commitment {
        return Err("receipts commitment".into());
    }
    if t.root_hash() != c.pre_state_root {
        return Err("pre_state_root".into());
    }
    let o = run_batch(c.block_height, c.block_gas_price, &mut t, &receipts)?;
    let ok = o.slice_post_root == c.slice_post_root
        && o.outcome_root == c.outcome_root
        && o.refund_count == c.refund_count
        && o.refunds_commitment == c.refunds_commitment
        && o.gas_burnt_total == c.gas_burnt_total
        && o.tokens_burnt_total == c.tokens_burnt_total;
    if ok {
        Ok(())
    } else {
        Err("outputs differ".into())
    }
}
