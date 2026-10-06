//! Independent Rust predicate for domain D1 (spec/near-chunk-validation-d1.md §4), the
//! per-transaction nearcore results used for coverage, and D1-specific mutants.
//!
//! D1 = D0 with `w.no_txs` / `c.no_tx_flags` lifted and replaced by the transaction-shape
//! conditions; `r.shape` / `r.success` / `e.distinct_ids` extend to the local receipts the
//! transactions create. Classification uses the oracle client's full state and stored
//! execution outcomes (not the Lean/Python implementations).

use crate::claim::Built;
use crate::enc::Claim;
use crate::mutate::{Judge, Mutant};
use near_client::Client;
use near_crypto::{KeyType, PublicKey, Signature};
use near_primitives::action::Action;
use near_primitives::errors::TxExecutionError;
use near_primitives::hash::CryptoHash;
use near_primitives::merkle::merklize;
use near_primitives::sharding::{EncodedShardChunkBody, ShardChunkHeader, TransactionReceipt};
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::transaction::{ExecutionStatus, SignedTransaction, Transaction, TransactionNonce};
use near_primitives::trie_key::TrieKey;
use near_primitives_core::account::id::AccountType;
use rand::Rng;
use rand::rngs::StdRng;
use reed_solomon_erasure::galois_8::ReedSolomon;
use std::collections::HashSet;

/// D1 transaction shape (`w.tx_shape`): V0, or V1 with a plain nonce (any nonce mode);
/// exactly one action, a Transfer; ED25519 public key and ED25519 signature.
pub fn tx_shape_ok(t: &SignedTransaction) -> bool {
    let plain_nonce = match &t.transaction {
        Transaction::V0(_) => true,
        Transaction::V1(v) => matches!(v.nonce, TransactionNonce::Nonce { .. }),
    };
    plain_nonce
        && t.transaction.actions().len() == 1
        && matches!(t.transaction.actions()[0], Action::Transfer(_))
        && matches!(t.transaction.public_key(), PublicKey::ED25519(_))
        && matches!(t.signature, Signature::ED25519(_))
}

/// nearcore's result for each transaction of the main transition (from the stored outcomes of
/// block B2): "success", "success_local", "skipped_duplicate", or the `InvalidTxError` variant.
pub fn tx_results(client: &Client, built: &Built, w: &ChunkStateWitness) -> Vec<String> {
    let b2 = built.blocks[built.b2].hash();
    let mut seen = HashSet::new();
    w.transactions()
        .iter()
        .map(|t| {
            let h = t.get_hash();
            if !seen.insert(h) {
                return "skipped_duplicate".to_string();
            }
            let outs = client.chain.chain_store().get_outcomes_by_id(&h).unwrap_or_default();
            match outs.into_iter().find(|o| &o.block_hash == b2) {
                None => "no_outcome".to_string(),
                Some(o) => match o.outcome_with_id.outcome.status {
                    ExecutionStatus::SuccessReceiptId(_) => {
                        if t.transaction.receiver_id() == t.transaction.signer_id() {
                            "success_local".into()
                        } else {
                            "success".into()
                        }
                    }
                    ExecutionStatus::Failure(TxExecutionError::InvalidTxError(e)) => {
                        let s = format!("{e:?}");
                        s.split(|c: char| c == ' ' || c == '{' || c == '(').next().unwrap_or("").to_string()
                    }
                    other => format!("other:{other:?}"),
                },
            }
        })
        .collect()
}

/// Violated D1 conditions (empty = in D1).
pub fn classify(
    client: &Client,
    built: &Built,
    w: &ChunkStateWitness,
    d0_violations: &[&'static str],
) -> Result<Vec<&'static str>, String> {
    let mut v: Vec<&'static str> =
        d0_violations.iter().copied().filter(|x| *x != "w.no_txs" && *x != "c.no_tx_flags").collect();
    let mut add = |s: &'static str| {
        if !v.contains(&s) {
            v.push(s)
        }
    };
    if w.transactions().iter().chain(w.new_transactions().iter()).any(|t| !tx_shape_ok(t)) {
        add("w.tx_shape");
    }
    let b2 = &built.blocks[built.b2];
    if b2.header().is_genesis() {
        return Ok(v);
    }
    let em = client.epoch_manager.as_ref();
    let layout = em.get_shard_layout(b2.header().epoch_id()).map_err(|e| e.to_string())?;
    let idx = layout.get_shard_index(built.shard_id).map_err(|e| e.to_string())?;
    let slot = b2.chunks().get(idx).ok_or("slot")?.clone();
    let pre_trie = client
        .runtime_adapter
        .get_trie_for_shard(built.shard_id, b2.header().prev_hash(), slot.prev_state_root(), false)
        .map_err(|e| e.to_string())?;
    // signers read by `process_transactions` (lib.rs:2034-2056: the account is looked up only
    // for a transaction that is not a duplicate, not expired, passed `validate_transaction`
    // and whose cost does not overflow): absent or AccountV1 (72 bytes, no V2 sentinel)
    let results = tx_results(client, built, w);
    for (t, r) in w.transactions().iter().zip(results.iter()) {
        if matches!(r.as_str(), "skipped_duplicate" | "Expired" | "InvalidSignature" | "CostOverflow") {
            continue;
        }
        let raw = pre_trie
            .get(&TrieKey::Account { account_id: t.transaction.signer_id().clone() }.to_vec(), near_store::trie::AccessOptions::DEFAULT)
            .map_err(|e| e.to_string())?;
        if let Some(r) = raw {
            if r.len() != 72 || r[..16] == [0xff; 16] {
                add("t.signer_v1");
            }
        }
    }
    // local receipts (receiver == signer): D0 receipt shape and success
    let mut ids: HashSet<CryptoHash> = HashSet::new();
    for (k, r) in w.source_receipt_proofs().values().flat_map(|p| p.0.iter()).enumerate() {
        let _ = k;
        ids.insert(*r.receipt_id());
    }
    for t in w.transactions() {
        if t.transaction.receiver_id() != t.transaction.signer_id() {
            continue;
        }
        let outs = client.chain.chain_store().get_outcomes_by_id(&t.get_hash()).unwrap_or_default();
        let Some(o) = outs.into_iter().find(|o| &o.block_hash == b2.hash()) else { continue };
        let ExecutionStatus::SuccessReceiptId(rid) = o.outcome_with_id.outcome.status else { continue };
        if !ids.insert(rid) {
            add("e.distinct_ids");
        }
        if t.transaction.receiver_id().get_account_type() != AccountType::NamedAccount {
            add("r.shape");
        }
        let routs = client.chain.chain_store().get_outcomes_by_id(&rid).unwrap_or_default();
        let ok = routs.into_iter().find(|o| &o.block_hash == b2.hash()).is_some_and(|o| {
            matches!(o.outcome_with_id.outcome.status, ExecutionStatus::SuccessValue(_))
        });
        if !ok {
            add("r.success");
        }
    }
    Ok(v)
}

fn v2(w: &mut ChunkStateWitness) -> &mut near_primitives::stateless_validation::state_witness::ChunkStateWitnessV2 {
    match w {
        ChunkStateWitness::V2(b) => b,
    }
}

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

/// D1 mutants of an honest D1 case. Witness mutants are judged by nearcore; `tx_valid`
/// mutants by nearcore with the trusted validity answers replaced (judge::nearcore_judge_flags).
/// Returns (mutant, in_d1 of the mutated pair as far as the shape is concerned).
pub fn mutants(client: &Client, claim: &Claim, w: &ChunkStateWitness, rng: &mut StdRng) -> Vec<(Mutant, Option<Vec<u8>>)> {
    let mut out: Vec<(Mutant, Option<Vec<u8>>)> = Vec::new();
    let enc = |w: &ChunkStateWitness| borsh::to_vec(w).unwrap();
    let ChunkStateWitness::V2(x) = w;
    let n = x.transactions.len();
    let push = |out: &mut Vec<(Mutant, Option<Vec<u8>>)>, name: String, claim: Claim, wb: Vec<u8>, flags: Option<Vec<u8>>| {
        out.push((Mutant { name, claim, witness: wb, judge: Judge::Nearcore }, flags))
    };
    // trusted tx_valid flags, each flipped (≤ 6)
    let mut idx: Vec<usize> = (0..n).collect();
    for _ in 0..n.min(6) {
        let j = rng.gen_range(0..idx.len());
        let i = idx.swap_remove(j);
        let mut c = claim.clone();
        c.tx_valid[i] ^= 1;
        let flags = c.tx_valid.clone();
        push(&mut out, format!("t.tx_valid_flip.{i}"), c, enc(w), Some(flags));
    }
    if n > 0 {
        // drop one transaction (and its flag)
        let i = rng.gen_range(0..n);
        let mut w2 = w.clone();
        v2(&mut w2).transactions.remove(i);
        let mut c = claim.clone();
        c.tx_valid.remove(i);
        let f = c.tx_valid.clone();
        push(&mut out, "w.tx.drop".into(), c, enc(&w2), Some(f));
        // signature bit flip (still decodable): tx_root no longer matches B2's chunk
        let mut w3 = w.clone();
        if let Signature::ED25519(s) = &v2(&mut w3).transactions[i].signature {
            let mut b = s.to_bytes();
            b[rng.gen_range(0..32)] ^= 1;
            v2(&mut w3).transactions[i].signature = Signature::ED25519(ed25519_dalek::Signature::from_bytes(&b));
            push(&mut out, "w.tx.sig_flip".into(), claim.clone(), enc(&w3), None);
        }
        // signature with the borsh-rejected high bits: the witness does not decode
        let mut wb = enc(w);
        let pos = {
            // locate the tx's signature: re-encode the prefix up to and including tx i
            let mut pre = Vec::new();
            pre.push(1u8);
            pre.extend(borsh::to_vec(&x.epoch_id).unwrap());
            pre.extend(borsh::to_vec(&x.chunk_header).unwrap());
            pre.extend(borsh::to_vec(&x.main_state_transition).unwrap());
            pre.extend(borsh::to_vec(&x.source_receipt_proofs).unwrap());
            pre.extend(borsh::to_vec(&x.applied_receipts_hash).unwrap());
            pre.extend((n as u32).to_le_bytes());
            for t in &x.transactions[..=i] {
                pre.extend(borsh::to_vec(t).unwrap());
            }
            pre.len() - 1
        };
        if matches!(x.transactions[i].signature, Signature::ED25519(_)) {
            wb[pos] |= 0x20;
            push(&mut out, "w.tx.sig_high_bits(undecodable)".into(), claim.clone(), wb, None);
        }
        if n > 1 {
            let i = rng.gen_range(0..n - 1);
            if x.transactions[i] != x.transactions[i + 1] {
                let mut w4 = w.clone();
                v2(&mut w4).transactions.swap(i, i + 1);
                let mut c = claim.clone();
                c.tx_valid.swap(i, i + 1);
                let f = c.tx_valid.clone();
                push(&mut out, "w.tx.swap".into(), c, enc(&w4), Some(f));
            }
        }
    }
    // new_transactions: change them and re-hash the endorsed header (tx_root, encoded merkle
    // root/length) in both the claim and the witness: nearcore checks no signature here
    let m = x.new_transactions.len();
    if m > 0 {
        let chunk_hash = w.chunk_header().chunk_hash().clone();
        if let Ok(chunk) = client.chain.get_chunk(&chunk_hash) {
            let receipts = chunk.prev_outgoing_receipts().to_vec();
            let d = client.epoch_manager.num_data_parts();
            let total = client.epoch_manager.num_total_parts();
            let rs = ReedSolomon::new(d, total - d).unwrap();
            let rehash = |txs: Vec<SignedTransaction>| -> Option<(Claim, Vec<u8>)> {
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
                Some((c, borsh::to_vec(&w2).unwrap()))
            };
            let i = rng.gen_range(0..m);
            let mut t1 = x.new_transactions.clone();
            if let Signature::ED25519(s) = &t1[i].signature {
                let mut b = s.to_bytes();
                b[rng.gen_range(0..32)] ^= 1;
                t1[i].signature = Signature::ED25519(ed25519_dalek::Signature::from_bytes(&b));
                if let Some((c, wb)) = rehash(t1) {
                    push(&mut out, "w.new_tx.sig_flip_rehashed".into(), c, wb, None);
                }
            }
            let mut t2 = x.new_transactions.clone();
            t2.remove(i);
            if let Some((c, wb)) = rehash(t2) {
                push(&mut out, "w.new_tx.drop_rehashed".into(), c, wb, None);
            }
            // header-only change: the witness's new_transactions no longer match tx_root
            let mut t3 = x.new_transactions.clone();
            t3.remove(i);
            let mut w5 = w.clone();
            v2(&mut w5).new_transactions = t3;
            push(&mut out, "w.new_tx.drop".into(), claim.clone(), enc(&w5), None);
        }
    }
    let _ = KeyType::ED25519;
    out
}
