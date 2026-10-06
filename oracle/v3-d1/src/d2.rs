//! Independent Rust predicate for domain D2 (spec/near-chunk-validation-v0.md §6 D2;
//! `InD1 ⊂ InD2`), per-receipt / per-action coverage labels, and D2 mutants.
//!
//! D2 keeps the D0 conditions `c.pv86` (every epoch), `c.layout`, `c.headers`,
//! `c.not_genesis`, `c.segment`, `w.no_code`, `w.size`; replaces `c.single_epoch` by
//! `c.same_layout` (every epoch of the claim has the endorsed epoch's shard layout and no
//! outgoing buffer targets a shard outside it: no resharding) and `c.no_split_gate` by its
//! split-gate half (validator updates are inside D2); lifts `w.no_txs`, `c.no_tx_flags`,
//! `c.own_congestion_zero`, `e.queues_empty`, `e.compute`, `e.forwarded`, `r.shape`,
//! `r.success`, `r.refunds`, `t.signer_v1`, `e.distinct_ids`; and adds (the shared D2 contract,
//! spec/near-chunk-validation-d2.md §12):
//!   * `w.shape`  every transaction (both lists) has an ED25519 key and signature; no
//!                DeployGlobalContract / UseGlobalContract / DeterministicStateInit action, no
//!                GlobalContractDistribution receipt and no ML-DSA-65 key in any transaction or
//!                receipt the main transition decodes;
//!   * `e.wasm`   no FunctionCall action reaches its dispatch point (receiver exists, earlier
//!                actions of the receipt succeeded) in a receipt the main transition executes
//!                (local, delayed, incoming, instant, postponed receipt completed by its data,
//!                resumed PromiseYield receipt) — receipts that are only converted, stored or
//!                moved may carry FunctionCalls;
//!   * `e.secp`   no SECP256K1 delegate signature is verified;
//!   * `w.size`   also sum(base_state) + 2000 · (ContractData removals) ≤ 4 000 000 (the
//!                storage-proof soft limit can never stop receipt processing).
//! Classification uses the oracle client's full state and stored execution outcomes.

use crate::chaingen::{GenOpts, Stats};
use crate::claim::{Built, block_rec};
use crate::enc::Claim;
use crate::judge::nearcore_judge;
use crate::mutate::{Judge, Mutant, drop_each_node, mutants};
use near_chain::ChainStoreAccess;
use near_chain::stateless_validation::chunk_validation::MainTransition;
use near_client::Client;
use near_crypto::{KeyType, PublicKey, Signature};
use near_primitives::action::Action;
use near_primitives::errors::{ActionErrorKind, TxExecutionError};
use near_primitives::hash::CryptoHash;
use near_primitives::receipt::{Receipt, ReceiptEnum, ReceiptSource, VersionedReceiptEnum};
use near_primitives::sharding::{ShardChunkHeader, ShardChunkHeaderInner};
use near_primitives::state::PartialState;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::transaction::{ExecutionStatus, SignedTransaction};
use near_primitives::trie_key::TrieKey;
use near_primitives::types::AccountId;
use near_primitives_core::account::id::AccountType;
use near_store::Trie;
use rand::Rng;
use rand::rngs::StdRng;
use serde_json::json;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::Path;

/// Global-contract / state-init actions (anywhere, also inside delegates): `w.shape`.
fn forbidden(a: &Action) -> bool {
    match a {
        Action::DeployGlobalContract(_) | Action::UseGlobalContract(_) | Action::DeterministicStateInit(_) => true,
        Action::Delegate(d) => d.delegate_action.get_actions().iter().any(forbidden),
        Action::DelegateV2(d) => d.delegate_action.get_actions().iter().any(forbidden),
        _ => false,
    }
}

fn mldsa(pk: &PublicKey) -> bool {
    matches!(pk.key_type(), KeyType::MLDSA65)
}

fn action_keys_ok(a: &Action) -> bool {
    match a {
        Action::AddKey(x) => !mldsa(&x.public_key),
        Action::DeleteKey(x) => !mldsa(&x.public_key),
        Action::Stake(x) => !mldsa(&x.public_key),
        Action::TransferToGasKey(x) => !mldsa(&x.public_key),
        Action::WithdrawFromGasKey(x) => !mldsa(&x.public_key),
        Action::Delegate(d) => {
            !mldsa(&d.delegate_action.public_key)
                && !matches!(d.signature, Signature::MLDSA65(_))
                && d.delegate_action.get_actions().iter().all(action_keys_ok)
        }
        Action::DelegateV2(d) => {
            !mldsa(d.delegate_action.public_key())
                && !matches!(d.signature, Signature::MLDSA65(_))
                && d.delegate_action.get_actions().iter().all(action_keys_ok)
        }
        _ => true,
    }
}

/// D2 transaction shape (`w.shape` for transactions).
pub fn tx_shape_ok(t: &SignedTransaction) -> bool {
    matches!(t.transaction.public_key(), PublicKey::ED25519(_))
        && matches!(t.signature, Signature::ED25519(_))
        && t.transaction.actions().iter().all(|a| !forbidden(a) && action_keys_ok(a))
}

fn action_name(a: &Action) -> String {
    match a {
        Action::CreateAccount(_) => "CreateAccount".into(),
        Action::DeployContract(_) => "DeployContract".into(),
        Action::FunctionCall(_) => "FunctionCall".into(),
        Action::Transfer(_) => "Transfer".into(),
        Action::Stake(s) => if s.stake.is_zero() { "Unstake".into() } else { "Stake".into() },
        Action::AddKey(k) => match &k.access_key.permission {
            near_primitives::account::AccessKeyPermission::FullAccess => "AddKey(full)".into(),
            near_primitives::account::AccessKeyPermission::FunctionCall(_) => "AddKey(fc)".into(),
            _ => "AddKey(gas)".into(),
        },
        Action::DeleteKey(_) => "DeleteKey".into(),
        Action::DeleteAccount(_) => "DeleteAccount".into(),
        Action::Delegate(d) => format!("Delegate[{}]", d.delegate_action.get_actions().iter().map(action_name).collect::<Vec<_>>().join(",")),
        Action::DelegateV2(d) => format!("DelegateV2[{}]", d.delegate_action.get_actions().iter().map(action_name).collect::<Vec<_>>().join(",")),
        Action::DeployGlobalContract(_) => "DeployGlobalContract".into(),
        Action::UseGlobalContract(_) => "UseGlobalContract".into(),
        Action::DeterministicStateInit(_) => "DeterministicStateInit".into(),
        Action::TransferToGasKey(_) => "TransferToGasKey".into(),
        Action::WithdrawFromGasKey(_) => "WithdrawFromGasKey".into(),
    }
}

fn status_name(s: &ExecutionStatus) -> String {
    match s {
        ExecutionStatus::SuccessValue(_) => "ok".into(),
        ExecutionStatus::SuccessReceiptId(_) => "ok_receipt".into(),
        ExecutionStatus::Failure(TxExecutionError::ActionError(e)) => {
            let k = format!("{:?}", e.kind);
            format!("fail:{}", k.split(|c: char| c == ' ' || c == '{' || c == '(').next().unwrap_or(""))
        }
        ExecutionStatus::Failure(TxExecutionError::InvalidTxError(e)) => {
            let k = format!("{e:?}");
            format!("invalid:{}", k.split(|c: char| c == ' ' || c == '{' || c == '(').next().unwrap_or(""))
        }
        ExecutionStatus::Unknown => "unknown".into(),
    }
}

/// Everything the classifier and the coverage labels need about the main transition.
pub struct Analysis {
    pub violations: Vec<&'static str>,
    pub action_results: Vec<String>,
    pub receipt_classes: BTreeMap<String, u64>,
    pub features: BTreeMap<String, serde_json::Value>,
    /// facts read: executed Stake (amount, success, InsufficientStake?)
    pub stakes: Vec<(u128, bool, bool)>,
    pub eth_created: bool,
}

fn queue_idx(t: &Trie) -> Result<((u64, u64), BTreeMap<u64, (u64, u64)>, (u64, u64)), String> {
    let e = |x: near_store::StorageError| x.to_string();
    let d = near_store::get_delayed_receipt_indices(t).map_err(e)?;
    let b = near_store::get_buffered_receipt_indices(t).map_err(e)?;
    let y = near_store::get_promise_yield_indices(t).map_err(e)?;
    Ok((
        (d.first_index, d.next_available_index),
        b.shard_buffers.iter().map(|(k, q)| (k.to_string().parse::<u64>().unwrap(), (q.first_index, q.next_available_index))).collect(),
        (y.first_index, y.next_available_index),
    ))
}

fn count_prefix(t: &Trie, prefix: &[u8]) -> Result<u64, String> {
    let mut it = t.disk_iter().map_err(|e| e.to_string())?;
    it.seek_prefix(prefix).map_err(|e| e.to_string())?;
    let mut n = 0;
    for x in it {
        let (k, _) = x.map_err(|e| e.to_string())?;
        if !k.starts_with(prefix) {
            break;
        }
        n += 1;
    }
    Ok(n)
}

pub fn analyze(client: &Client, built: &Built, w: &ChunkStateWitness, d0_violations: &[&'static str], base_bytes: usize) -> Result<Analysis, String> {
    let lifted = [
        "w.no_txs", "c.no_tx_flags", "c.own_congestion_zero", "e.queues_empty", "e.compute", "e.forwarded", "r.shape",
        "r.success", "r.refunds", "c.single_epoch", "c.no_split_gate", "e.distinct_ids",
    ];
    let mut v: Vec<&'static str> = d0_violations.iter().copied().filter(|x| !lifted.contains(x)).collect();
    let mut add = |v: &mut Vec<&'static str>, s: &'static str| {
        if !v.contains(&s) {
            v.push(s)
        }
    };
    let c = &built.claim;
    let mut an = Analysis {
        violations: vec![],
        action_results: vec![],
        receipt_classes: BTreeMap::new(),
        features: BTreeMap::new(),
        stakes: vec![],
        eth_created: false,
    };
    if c.apply_facts.iter().any(|f| f.split_gate.is_some()) {
        add(&mut v, "c.no_split_gate");
    }
    if c.epochs.iter().any(|e| e.shard_layout != c.epochs.iter().find(|x| x.epoch_id == c.epoch_id).unwrap().shard_layout) {
        add(&mut v, "c.same_layout");
    }
    if w.transactions().iter().chain(w.new_transactions().iter()).any(|t| !tx_shape_ok(t)) {
        add(&mut v, "w.shape");
    }
    an.features.insert("n_epochs".into(), json!(c.epochs.len()));
    an.features.insert("validator_updates".into(), json!(c.apply_facts.iter().filter(|f| f.validator_update.is_some()).count()));
    an.features.insert("validator_update_in_main".into(), json!(c.apply_facts.first().is_some_and(|f| f.validator_update.is_some())));
    let b2 = &built.blocks[built.b2];
    if b2.header().is_genesis() {
        an.violations = v;
        return Ok(an);
    }
    let em = client.epoch_manager.as_ref();
    let layout = em.get_shard_layout(b2.header().epoch_id()).map_err(|e| e.to_string())?;
    let sid = built.shard_id;
    let idx = layout.get_shard_index(sid).map_err(|e| e.to_string())?;
    let slot = b2.chunks().get(idx).ok_or("slot")?.clone();
    let rt = client.runtime_adapter.as_ref();
    let pre = rt.get_trie_for_shard(sid, b2.header().prev_hash(), slot.prev_state_root(), false).map_err(|e| e.to_string())?;
    let uid = near_primitives::shard_layout::ShardUId::from_shard_id_and_layout(sid, &layout);
    let extra = client.chain.get_chunk_extra(b2.hash(), &uid).map_err(|e| e.to_string())?;
    let post = rt.get_trie_for_shard(sid, b2.hash(), *extra.state_root(), false).map_err(|e| e.to_string())?;
    let pv = crate::judge::pre_validate(client, w)?;
    let incoming: Vec<Receipt> = match pv.main_transition_params {
        MainTransition::NewChunk { new_chunk_data, .. } => new_chunk_data.receipts,
        MainTransition::Genesis { .. } => vec![],
    };
    // ---- receipts by id
    let store = client.chain.chain_store();
    let mut by_id: HashMap<CryptoHash, (Receipt, String)> = HashMap::new();
    for r in &incoming {
        let cls = match r.receipt() {
            ReceiptEnum::Action(_) | ReceiptEnum::ActionV2(_) => {
                if r.predecessor_id().is_system() { "incoming_refund" } else { "incoming_action" }
            }
            ReceiptEnum::Data(_) => "incoming_data",
            ReceiptEnum::PromiseYield(_) | ReceiptEnum::PromiseYieldV2(_) => "incoming_promise_yield",
            ReceiptEnum::PromiseResume(_) => "incoming_promise_resume",
            ReceiptEnum::GlobalContractDistribution(_) => {
                add(&mut v, "w.shape");
                "incoming_global_contract"
            }
        };
        *an.receipt_classes.entry(cls.into()).or_default() += 1;
        if let ReceiptEnum::Action(a) = r.receipt() {
            if !a.input_data_ids.is_empty() {
                *an.receipt_classes.entry("incoming_with_input_data".into()).or_default() += 1;
            }
        }
        if !receipt_shape_ok(r) {
            add(&mut v, "w.shape");
        }
        by_id.insert(*r.receipt_id(), (r.clone(), "incoming".into()));
    }
    let processed = store.get_processed_receipt_ids(b2.hash(), sid).map(|x| (*x).clone()).unwrap_or_default();
    for m in &processed {
        let src = match m.source() {
            ReceiptSource::Local => "local",
            ReceiptSource::Delayed => "delayed_popped",
            ReceiptSource::Instant => "instant",
            ReceiptSource::ReceiptToTxGc => continue,
        };
        *an.receipt_classes.entry(src.into()).or_default() += 1;
        if let Some(r) = store.get_receipt(m.receipt_id()) {
            by_id.insert(*m.receipt_id(), ((*r).clone(), src.into()));
        }
    }
    let tx_hashes: HashSet<CryptoHash> = w.transactions().iter().map(|t| t.get_hash()).collect();
    let outcome_ids = near_store::adapter::StoreAdapter::chain_store(&client.chain.chain_store().store()).get_outcomes_by_block_hash_and_shard_id(b2.hash(), sid);
    let mut executed = 0u64;
    for id in &outcome_ids {
        if tx_hashes.contains(id) {
            continue;
        }
        let outs = store.get_outcomes_by_id(id).map_err(|e| format!("{e:?}"))?;
        let Some(o) = outs.into_iter().find(|o| &o.block_hash == b2.hash()) else { continue };
        let outcome = o.outcome_with_id.outcome;
        let executor = outcome.executor_id.clone();
        let (r, src) = match by_id.get(id) {
            Some(x) => x.clone(),
            None => match near_store::get_postponed_receipt(&pre, &executor, *id).map_err(|e| e.to_string())? {
                Some(r) => {
                    *an.receipt_classes.entry("postponed_executed".into()).or_default() += 1;
                    (r, "postponed".into())
                }
                None => match find_yield_receipt(&pre, &executor, id)? {
                    Some(r) => {
                        *an.receipt_classes.entry("yield_resumed".into()).or_default() += 1;
                        (r, "yield_resumed".into())
                    }
                    None => {
                        add(&mut v, "e.wasm");
                        *an.receipt_classes.entry("executed_unknown".into()).or_default() += 1;
                        continue;
                    }
                },
            },
        };
        executed += 1;
        let (actions, signer_pk) = match r.versioned_receipt() {
            VersionedReceiptEnum::Action(a) | VersionedReceiptEnum::PromiseYield(a) => {
                (a.actions().to_vec(), Some(a.signer_public_key().clone()))
            }
            _ => (vec![], None),
        };
        if actions.iter().any(forbidden) || signer_pk.as_ref().is_some_and(mldsa) || !actions.iter().all(action_keys_ok) {
            add(&mut v, "w.shape");
        }
        // dispatch point: actions before the failing one, and the failing one unless it failed
        // the existence check (AccountDoesNotExist), were dispatched
        let reached = |j: usize| -> bool {
            match &outcome.status {
                ExecutionStatus::Failure(TxExecutionError::ActionError(e)) => match e.index {
                    None => true,
                    Some(i) => (j as u64) < i || ((j as u64) == i && !matches!(e.kind, ActionErrorKind::AccountDoesNotExist { .. })),
                },
                _ => true,
            }
        };
        for (j, a) in actions.iter().enumerate() {
            match a {
                Action::FunctionCall(_) if reached(j) => add(&mut v, "e.wasm"),
                Action::Delegate(d) if reached(j) && matches!((&d.delegate_action.public_key, &d.signature), (PublicKey::SECP256K1(_), Signature::SECP256K1(_))) => add(&mut v, "e.secp"),
                Action::DelegateV2(d) if reached(j) && matches!((d.delegate_action.public_key(), &d.signature), (PublicKey::SECP256K1(_), Signature::SECP256K1(_))) => add(&mut v, "e.secp"),
                _ => {}
            }
        }
        let st = status_name(&outcome.status);
        let is_refund = r.predecessor_id().is_system();
        let names: Vec<String> = actions.iter().map(action_name).collect();
        an.action_results.push(format!("{}{}:[{}] => {}", src, if is_refund { "(refund)" } else { "" }, names.join(","), st));
        for a in &actions {
            if let Action::Stake(s) = a {
                if !s.stake.is_zero() {
                    let insufficient = matches!(&outcome.status, ExecutionStatus::Failure(TxExecutionError::ActionError(e)) if matches!(e.kind, ActionErrorKind::InsufficientStake { .. }));
                    an.stakes.push((s.stake.as_yoctonear(), matches!(outcome.status, ExecutionStatus::SuccessValue(_)), insufficient));
                }
            }
        }
        if !is_refund
            && actions.len() == 1
            && matches!(actions[0], Action::Transfer(_))
            && r.receiver_id().get_account_type() == AccountType::EthImplicitAccount
            && matches!(outcome.status, ExecutionStatus::SuccessValue(_))
            && near_store::get_account(&pre, r.receiver_id()).map_err(|e| e.to_string())?.is_none()
        {
            an.eth_created = true;
        }
    }
    an.features.insert("executed_receipts".into(), json!(executed));
    // ---- distinct ids: incoming and local
    let mut ids: HashSet<CryptoHash> = HashSet::new();
    for r in incoming.iter() {
        if !ids.insert(*r.receipt_id()) {
            add(&mut v, "e.distinct_ids");
        }
    }
    for m in &processed {
        if matches!(m.source(), ReceiptSource::Local) && !ids.insert(*m.receipt_id()) {
            add(&mut v, "e.distinct_ids");
        }
    }
    // ---- queues: delayed, buffers, yields (pre vs post)
    let (d0, b0, y0) = queue_idx(&pre)?;
    let (d1, b1, y1) = queue_idx(&post)?;
    let delayed_pushed = d1.1 - d0.1;
    if delayed_pushed > 0 {
        an.receipt_classes.insert("delayed_pushed".into(), delayed_pushed);
    }
    let (mut bp, mut bf) = (0, 0);
    for (k, (f1, n1)) in &b1 {
        let (f0, n0) = b0.get(k).copied().unwrap_or((0, 0));
        bp += n1 - n0;
        bf += f1 - f0;
    }
    if bp > 0 {
        an.receipt_classes.insert("buffered_pushed".into(), bp);
    }
    if bf > 0 {
        an.receipt_classes.insert("buffered_forwarded".into(), bf);
    }
    if y1.0 > y0.0 {
        an.receipt_classes.insert("yield_timeouts".into(), y1.0 - y0.0);
    }
    an.features.insert("delayed_queue_pre".into(), json!(d0.1 - d0.0));
    an.features.insert("delayed_queue_post".into(), json!(d1.1 - d1.0));
    an.features.insert("buffered_pre".into(), json!(b0.values().map(|(f, n)| n - f).sum::<u64>()));
    an.features.insert("buffered_post".into(), json!(b1.values().map(|(f, n)| n - f).sum::<u64>()));
    an.features.insert("yield_queue_pre".into(), json!(y0.1 - y0.0));
    // postponed receipts stored: PendingDataCount entries created (pre vs post count)
    let pend0 = count_prefix(&pre, &[col::PENDING_DATA_COUNT])?;
    let pend1 = count_prefix(&post, &[col::PENDING_DATA_COUNT])?;
    an.features.insert("pending_data_count_pre".into(), json!(pend0));
    an.features.insert("pending_data_count_post".into(), json!(pend1));
    let rd0 = count_prefix(&pre, &[col::RECEIVED_DATA])?;
    let rd1 = count_prefix(&post, &[col::RECEIVED_DATA])?;
    an.features.insert("received_data_pre".into(), json!(rd0));
    an.features.insert("received_data_post".into(), json!(rd1));
    // ---- outgoing receipts of the main transition (the endorsed chunk's prev_outgoing_receipts)
    if let Ok(chunk) = client.chain.get_chunk(&w.chunk_header().chunk_hash()) {
        for r in chunk.prev_outgoing_receipts() {
            let cls = match r.receipt() {
                ReceiptEnum::Action(_) | ReceiptEnum::ActionV2(_) => {
                    if r.predecessor_id().is_system() { "out_refund" } else { "out_action" }
                }
                ReceiptEnum::Data(_) => "out_data",
                ReceiptEnum::PromiseResume(_) => "out_promise_resume",
                _ => "out_other",
            };
            *an.receipt_classes.entry(cls.into()).or_default() += 1;
        }
    }
    // ---- endorsed header features
    let h = w.chunk_header();
    an.features.insert("header_validator_proposals".into(), json!(h.prev_validator_proposals().count()));
    an.features.insert(
        "header_bandwidth_requests".into(),
        json!(h.bandwidth_requests().map_or(0, |r| match r { near_primitives::bandwidth_scheduler::BandwidthRequests::V1(v) => v.requests.len() })),
    );
    let ci = h.congestion_info();
    an.features.insert("own_congestion_nonzero_post".into(), json!(ci.delayed_receipts_gas() != 0 || ci.buffered_receipts_gas() != 0 || ci.receipt_bytes() != 0));
    let ci0 = slot.congestion_info();
    an.features.insert("own_congestion_nonzero_pre".into(), json!(ci0.delayed_receipts_gas() != 0 || ci0.buffered_receipts_gas() != 0 || ci0.receipt_bytes() != 0));
    // ---- storage-proof soft limit: ContractData removals (keys present in pre, absent in post)
    let mut removals = 0u64;
    {
        let mut it = pre.disk_iter().map_err(|e| e.to_string())?;
        it.seek_prefix(&[col::CONTRACT_DATA]).map_err(|e| e.to_string())?;
        for x in it {
            let (k, _) = x.map_err(|e| e.to_string())?;
            if k.first() != Some(&col::CONTRACT_DATA) {
                break;
            }
            if post.get(&k, near_store::trie::AccessOptions::DEFAULT).map_err(|e| e.to_string())?.is_none() {
                removals += 1;
            }
        }
    }
    an.features.insert("contract_data_removals".into(), json!(removals));
    if base_bytes as u64 + 2000 * removals > 4_000_000 {
        add(&mut v, "w.size");
    }
    // c.same_layout: no non-empty outgoing buffer to a shard outside the layout
    if b0.iter().any(|(k, (f, n))| f != n && layout.get_shard_index(near_primitives::types::ShardId::new(*k)).is_err()) {
        add(&mut v, "c.same_layout");
    }
    if c.epochs.iter().any(|e| e.protocol_version != 86) {
        add(&mut v, "c.pv86");
    }
    an.violations = v;
    Ok(an)
}

fn receipt_shape_ok(r: &Receipt) -> bool {
    match r.versioned_receipt() {
        VersionedReceiptEnum::Action(a) | VersionedReceiptEnum::PromiseYield(a) => {
            !mldsa(a.signer_public_key()) && a.actions().iter().all(|x| !forbidden(x) && action_keys_ok(x))
        }
        VersionedReceiptEnum::GlobalContractDistribution(_) => false,
        _ => true,
    }
}

/// The PromiseYield receipt with this receipt id stored for `account` in the pre-state.
fn find_yield_receipt(pre: &Trie, account: &AccountId, id: &CryptoHash) -> Result<Option<Receipt>, String> {
    let mut prefix = vec![col::PROMISE_YIELD_RECEIPT];
    prefix.extend(account.as_bytes());
    prefix.push(b',');
    let mut it = pre.disk_iter().map_err(|e| e.to_string())?;
    it.seek_prefix(&prefix).map_err(|e| e.to_string())?;
    for x in it {
        let (k, v) = x.map_err(|e| e.to_string())?;
        if !k.starts_with(&prefix) {
            break;
        }
        if let Ok(r) = borsh::from_slice::<Receipt>(&v) {
            if r.receipt_id() == id {
                return Ok(Some(r));
            }
        }
    }
    Ok(None)
}

mod col {
    pub const PROMISE_YIELD_RECEIPT: u8 = 12;
    pub const RECEIVED_DATA: u8 = 3;
    pub const PENDING_DATA_COUNT: u8 = 5;
    pub const CONTRACT_DATA: u8 = 9;
}

/// nearcore's result for each transaction of the main transition (D1's, extended with the
/// gas-key deposit-failure outcome).
pub fn tx_results(client: &Client, built: &Built, w: &ChunkStateWitness) -> Vec<String> {
    crate::d1::tx_results(client, built, w)
}

// ---------------------------------------------------------------------------------------------
// mutants
// ---------------------------------------------------------------------------------------------

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

/// Header mutants re-encoding the endorsed inner (validator proposals, congestion info,
/// bandwidth requests), claim and witness changed together; judged by nearcore.
fn header_mutants(claim: &Claim, w: &ChunkStateWitness, rng: &mut StdRng) -> Vec<Mutant> {
    let mut out = Vec::new();
    let Ok(inner) = borsh::from_slice::<ShardChunkHeaderInner>(&claim.chunk_inner) else { return out };
    let ShardChunkHeaderInner::V5(x) = inner else { return out };
    let mut push = |name: &str, y: near_primitives::sharding::shard_chunk_header_inner::ShardChunkHeaderInnerV5| {
        let b = borsh::to_vec(&ShardChunkHeaderInner::V5(y)).unwrap();
        if let Some(w2) = with_inner(w, &b) {
            let mut c2 = claim.clone();
            c2.chunk_inner = b;
            out.push(Mutant { name: name.into(), claim: c2, witness: borsh::to_vec(&w2).unwrap(), judge: Judge::Nearcore });
        }
    };
    use near_primitives::types::validator_stake::ValidatorStake;
    if !x.prev_validator_proposals.is_empty() {
        let mut y = x.clone();
        let i = rng.gen_range(0..y.prev_validator_proposals.len());
        y.prev_validator_proposals.remove(i);
        push("hdr2.proposals.drop", y);
        let mut y = x.clone();
        let p = &y.prev_validator_proposals[i];
        let st = near_primitives::types::Balance::from_yoctonear(p.stake().as_yoctonear() ^ 1);
        y.prev_validator_proposals[i] = ValidatorStake::new(p.account_id().clone(), p.public_key().clone(), st);
        push("hdr2.proposals.stake_flip", y);
        if x.prev_validator_proposals.len() > 1 {
            let mut y = x.clone();
            y.prev_validator_proposals.reverse();
            push("hdr2.proposals.reorder", y);
        }
    }
    {
        let ci = x.congestion_info;
        let near_primitives::congestion_info::CongestionInfo::V1(c1) = ci;
        if c1.buffered_receipts_gas != 0 || c1.delayed_receipts_gas != 0 || c1.receipt_bytes != 0 {
            let mut y = x.clone();
            let near_primitives::congestion_info::CongestionInfo::V1(ref mut c) = y.congestion_info;
            c.buffered_receipts_gas ^= 1;
            push("hdr2.congestion.buffered_gas", y);
            let mut y = x.clone();
            let near_primitives::congestion_info::CongestionInfo::V1(ref mut c) = y.congestion_info;
            c.receipt_bytes = c.receipt_bytes.wrapping_add(1);
            push("hdr2.congestion.receipt_bytes", y);
        }
    }
    {
        let near_primitives::bandwidth_scheduler::BandwidthRequests::V1(br) = &x.bandwidth_requests;
        if !br.requests.is_empty() {
            let mut y = x.clone();
            let near_primitives::bandwidth_scheduler::BandwidthRequests::V1(ref mut b) = y.bandwidth_requests;
            b.requests.pop();
            push("hdr2.bandwidth_requests.drop", y);
            let mut y = x.clone();
            let near_primitives::bandwidth_scheduler::BandwidthRequests::V1(ref mut b) = y.bandwidth_requests;
            let j = rng.gen_range(0..b.requests.len());
            let bit = rng.gen_range(0..40u32);
            b.requests[j].requested_values_bitmap.data[(bit / 8) as usize] ^= 1 << (bit % 8);
            push("hdr2.bandwidth_requests.bitmap_flip", y);
        }
    }
    out
}

/// Trusted-fact mutants whose relation verdict is derived from nearcore's semantics (the
/// judge cannot be run with a different fact): see `write_d2_case`.
fn fact_mutants(built: &Built, an: &Analysis, shard_accounts: &dyn Fn(&str) -> bool) -> Vec<(Mutant, &'static str)> {
    let mut out = Vec::new();
    let c = &built.claim;
    let enc_w: Vec<u8> = Vec::new();
    let _ = enc_w;
    // minimum stake raised just above an executed successful stake ⇒ InsufficientStake ⇒ reject
    if let Some(s) = an.stakes.iter().filter(|x| x.1).map(|x| x.0).min() {
        let mut c2 = c.clone();
        c2.apply_facts[0].minimum_stake = s + 1;
        out.push((Mutant { name: "t.minimum_stake.raise(derived)".into(), claim: c2, witness: vec![], judge: Judge::Nearcore }, "reject"));
    }
    // minimum stake lowered to a stake that failed with InsufficientStake ⇒ succeeds ⇒ reject
    if let Some(s) = an.stakes.iter().filter(|x| x.2).map(|x| x.0).max() {
        let mut c2 = c.clone();
        c2.apply_facts[0].minimum_stake = s;
        out.push((Mutant { name: "t.minimum_stake.lower(derived)".into(), claim: c2, witness: vec![], judge: Judge::Nearcore }, "reject"));
    }
    // chain id → mainnet: the ETH-implicit wallet global contract hash changes ⇒ reject
    if an.eth_created {
        let mut c2 = c.clone();
        c2.chain_id = "mainnet".into();
        out.push((Mutant { name: "t.chain_id.mainnet(derived)".into(), claim: c2, witness: vec![], judge: Judge::Nearcore }, "reject"));
    }
    // validator rewards: +1 for an account of this shard in stake_info ⇒ locked differs ⇒ reject;
    // for an account of another shard: unread ⇒ the honest verdict
    for (i, f) in c.apply_facts.iter().enumerate() {
        let Some(vu) = &f.validator_update else { continue };
        let stake: HashSet<&String> = vu.stake_info.iter().map(|x| &x.0).collect();
        if let Some(j) = vu.validator_rewards.iter().position(|(a, _)| stake.contains(a) && shard_accounts(a)) {
            let mut c2 = c.clone();
            let vu2 = c2.apply_facts[i].validator_update.as_mut().unwrap();
            vu2.validator_rewards[j].1 += 1;
            out.push((Mutant { name: format!("t.validator_reward.own_shard.{i}(derived)"), claim: c2, witness: vec![], judge: Judge::Nearcore }, "reject"));
        }
        if let Some(j) = vu.validator_rewards.iter().position(|(a, _)| !shard_accounts(a)) {
            let mut c2 = c.clone();
            let vu2 = c2.apply_facts[i].validator_update.as_mut().unwrap();
            vu2.validator_rewards[j].1 += 1;
            out.push((Mutant { name: format!("t.validator_reward.other_shard.{i}(unread)"), claim: c2, witness: vec![], judge: Judge::Nearcore }, "same"));
        }
    }
    out
}

pub struct D2Ctx<'a> {
    pub tracker: &'a Client,
    pub client: &'a Client,
    pub built: &'a Built,
    pub sw: &'a ChunkStateWitness,
    pub wb: &'a [u8],
    pub verdict: &'a Result<(), String>,
    pub viol: &'a [&'static str],
    pub labels: &'a HashMap<CryptoHash, String>,
    pub chain_idx: usize,
    pub params: &'a str,
    pub n_shards: usize,
    pub out: &'a Path,
    pub o: &'a GenOpts,
    pub rng: &'a mut StdRng,
    pub ood_count: &'a mut BTreeMap<String, usize>,
    pub d2_seen: &'a mut usize,
    pub round: u64,
    /// subset mode (public fixtures): keep an honest D2 case iff it adds a coverage key not
    /// seen before in this chain, or its name hashes to 0 mod `keep_every` (1 = keep all)
    pub keep_every: u64,
    pub seen_cov: &'a mut HashSet<String>,
    pub drop_cap: usize,
}

fn write_case(dir: &Path, claim: &Claim, witness: &[u8], meta: serde_json::Value) {
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("claim.bin"), claim.encode()).unwrap();
    std::fs::write(dir.join("witness.bin"), crate::enc::encode_witness(witness, &[])).unwrap();
    std::fs::write(dir.join("meta.json"), serde_json::to_string_pretty(&meta).unwrap()).unwrap();
}

/// Domain-D2 classification, metadata, mutants and writing of one honest witness.
pub fn write_d2_case(x: D2Ctx, stats: &mut Stats) {
    let D2Ctx { tracker, client, built, sw, wb, verdict, viol, labels, chain_idx, params, n_shards, out, o, rng, ood_count, d2_seen, round, keep_every, seen_cov, drop_cap } = x;
    let _ = round;
    let in_d0 = viol.is_empty();
    let viol1 = match crate::d1::classify(tracker, built, sw, viol) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("d1 classify failed: {e}");
            return;
        }
    };
    let in_d1 = viol1.is_empty();
    let PartialState::TrieValues(vals) = &sw.main_state_transition().base_state;
    let base_bytes: usize = vals.iter().map(|x| x.len()).sum();
    let an = match analyze(tracker, built, sw, viol, base_bytes) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("d2 analyze failed: {e}");
            return;
        }
    };
    let viol2 = an.violations.clone();
    let in_d2 = viol2.is_empty();
    if in_d1 && !in_d2 {
        panic!("D1 case outside D2: {viol2:?}");
    }
    let tx_results = tx_results(tracker, built, sw);
    let lab = |t: &SignedTransaction| labels.get(&t.get_hash()).cloned().unwrap_or_else(|| "unknown".into());
    let tx_labels: Vec<String> = sw.transactions().iter().map(lab).collect();
    let new_tx_labels: Vec<String> = sw.new_transactions().iter().map(lab).collect();
    let key = sw.chunk_production_key();
    let name = format!("{chain_idx:02}-h{}-s{}", key.height_created, key.shard_id);
    for v in &viol2 {
        *stats.by_violation.entry(v.to_string()).or_default() += 1;
    }
    let mut features = json!({
        "n_shards": n_shards,
        "rs": [built.claim.rs_data_parts, built.claim.rs_total_parts],
        "n_blocks": built.claim.blocks.len(),
        "n_implicit": built.implicit.len(),
        "n_source_blocks": built.source.len(),
        "n_receipts": match sw { ChunkStateWitness::V2(x) => x.source_receipt_proofs.values().map(|p| p.0.len()).sum::<usize>() },
        "bw_requests_in_context": built.blocks.iter().any(|b| b.chunks().iter_raw().any(|c| c.bandwidth_requests().map_or(false, |r| match r { near_primitives::bandwidth_scheduler::BandwidthRequests::V1(v) => !v.requests.is_empty() }))),
        "other_congestion_nonzero": built.blocks.iter().any(|b| b.chunks().iter_raw().any(|c| { let ci = c.congestion_info(); ci.delayed_receipts_gas() != 0 || ci.buffered_receipts_gas() != 0 || ci.receipt_bytes() != 0 })),
        "witness_bytes": wb.len(),
        "base_state_bytes": base_bytes,
    });
    for (k, v) in &an.features {
        features[k] = v.clone();
    }
    let meta = json!({
        "case": name, "kind": "honest", "chain_params": params,
        "nearcore": verdict.as_ref().map(|_| "ok".to_string()).unwrap_or_else(|e| e.clone()),
        "expected_rel": verdict.is_ok(),
        "in_d0": in_d0, "d0_violations": viol,
        "expected_rel_d0": verdict.is_ok() && in_d0,
        "in_d1": in_d1, "d1_violations": viol1,
        "expected_rel_d1": verdict.is_ok() && in_d1,
        "in_d2": in_d2, "d2_violations": viol2,
        "expected_rel_d2": verdict.is_ok() && in_d2,
        "tx_labels": tx_labels, "tx_results": tx_results, "new_tx_labels": new_tx_labels,
        "action_results": an.action_results, "receipt_classes": an.receipt_classes,
        "features": features,
    });
    if !in_d2 {
        let fam = viol2.join("+");
        let c = ood_count.entry(fam).or_default();
        if *c < o.ood_cap {
            *c += 1;
            stats.ood_written += 1;
            write_case(&out.join("ood").join(&name), &built.claim, wb, meta);
        }
        return;
    }
    if keep_every > 1 {
        let mut keys: Vec<String> = Vec::new();
        for (l, r) in meta["tx_labels"].as_array().unwrap().iter().zip(meta["tx_results"].as_array().unwrap()) {
            keys.push(format!("tx:{}=>{}", l.as_str().unwrap(), r.as_str().unwrap()));
        }
        for a in meta["action_results"].as_array().unwrap() {
            keys.push(format!("ar:{}", a.as_str().unwrap()));
        }
        for (k, _) in meta["receipt_classes"].as_object().unwrap() {
            keys.push(format!("rc:{k}"));
        }
        for k in ["validator_update_in_main", "own_congestion_nonzero_pre"] {
            if meta["features"][k].as_bool() == Some(true) {
                keys.push(format!("f:{k}"));
            }
        }
        for k in ["header_validator_proposals", "header_bandwidth_requests", "yield_queue_pre", "pending_data_count_pre", "contract_data_removals", "n_implicit"] {
            if meta["features"][k].as_u64().unwrap_or(0) > 0 {
                keys.push(format!("f:{k}"));
            }
        }
        if meta["features"]["n_epochs"].as_u64().unwrap_or(1) > 1 {
            keys.push("f:multi_epoch".into());
        }
        let novel = keys.iter().any(|k| !seen_cov.contains(k));
        let hashed = u64::from_le_bytes(crate::enc::sha256(name.as_bytes())[..8].try_into().unwrap()) % keep_every == 0;
        if !novel && !hashed {
            return;
        }
        seen_cov.extend(keys);
    }
    if in_d0 {
        stats.d0 += 1;
    }
    if in_d1 {
        stats.d1 += 1;
    }
    stats.positives += 1; // D2 cases
    write_case(&out.join("d2").join(&name), &built.claim, wb, meta);
    *d2_seen += 1;
    let me = o.mutate_every;
    if !(verdict.is_ok() && me > 0 && *d2_seen % me == 0) {
        return;
    }
    let last = built.blocks.last().unwrap();
    let parent = if last.header().is_genesis() { None } else { client.chain.get_block(last.header().prev_hash()).ok().and_then(|b| block_rec(&b).ok()) };
    let mut ms: Vec<(Mutant, Option<Vec<u8>>, Option<&'static str>)> = Vec::new();
    // D0 mutants; the trusted-fact ones that D2 reads are kept only when insensitive
    let m_cur = built.claim.apply_facts.first().map(|f| f.minimum_stake).unwrap_or(0);
    for m in mutants(&built.claim, sw, parent, rng) {
        if m.name.starts_with("t.minimum_stake") {
            let m2 = m.claim.apply_facts[0].minimum_stake;
            let lo = m_cur.min(m2);
            let hi = m_cur.max(m2);
            if an.stakes.iter().any(|s| s.0 >= lo && s.0 < hi) {
                continue;
            }
        }
        if m.name.starts_with("t.chain_id") && an.eth_created {
            let class = |c: &str| match c {
                "mainnet" | "mocknet" => 0,
                "testnet" => 1,
                _ => 2,
            };
            if class(&m.claim.chain_id) != class(&built.claim.chain_id) {
                continue;
            }
        }
        ms.push((m, None, None));
    }
    if *d2_seen % (me * 2) == 0 {
        ms.extend(drop_each_node(&built.claim, sw, drop_cap).into_iter().map(|m| (m, None, None)));
    }
    ms.extend(crate::d1::mutants(client, &built.claim, sw, rng).into_iter().map(|(m, f)| (m, f, None)));
    ms.extend(header_mutants(&built.claim, sw, rng).into_iter().map(|m| (m, None, None)));
    let layout = client.epoch_manager.get_shard_layout(&near_primitives::types::EpochId(CryptoHash(built.claim.epoch_id))).ok();
    let sid = built.shard_id;
    let on_shard = |a: &str| -> bool {
        let Some(l) = &layout else { return false };
        a.parse::<AccountId>().is_ok_and(|a| l.account_id_to_shard_id(&a) == sid)
    };
    for (m, how) in fact_mutants(built, &an, &on_shard) {
        let mut m = m;
        m.witness = wb.to_vec();
        ms.push((m, None, Some(how)));
    }
    for (m, flags, derived) in ms {
        let (exp, src): (Result<(), String>, String) = match (&m.judge, &flags, derived) {
            (_, _, Some("reject")) => (Err("derived: the changed trusted fact changes the main transition".into()), "derived".into()),
            (_, _, Some(_)) => (verdict.clone(), "nearcore(fact unread)".into()),
            (Judge::Claim, _, _) => (Err("claim-v3 discipline".to_string()), "claim-v3".into()),
            (Judge::Nearcore, None, _) => (nearcore_judge(client, &m.witness, &[], (m.claim.rs_data_parts, m.claim.rs_total_parts)), "nearcore".into()),
            (Judge::Nearcore, Some(f), _) => (
                crate::d1judge::nearcore_judge_flags(client, &m.witness, (m.claim.rs_data_parts, m.claim.rs_total_parts), f),
                "nearcore(tx_valid=claim)".into(),
            ),
        };
        let mname = format!("{name}-{}", m.name);
        let meta = json!({
            "case": mname, "kind": "mutant", "mutation": m.name, "base": name,
            "verdict_source": src,
            "nearcore": exp.as_ref().map(|_| "ok".to_string()).unwrap_or_else(|e| e.clone()),
            "expected_rel": exp.is_ok(),
            "in_d0": in_d0, "d0_violations": viol,
            "expected_rel_d0": exp.is_ok() && in_d0,
            "in_d1": in_d1,
            "expected_rel_d1": exp.is_ok() && in_d1,
            "in_d2": true,
            "expected_rel_d2": exp.is_ok(),
        });
        stats.mutants += 1;
        write_case(&out.join("mutants").join(&mname), &m.claim, &m.witness, meta);
    }
    let _ = TrieKey::DelayedReceiptIndices;
}
