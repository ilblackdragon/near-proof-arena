//! Scope v2: `near/pv86/receipt-transfer-batch/v1` (challenge `near-transfer-receipt-v2`).
//!
//! Same receipt semantics as v1, but the claim's `post_state_root` is the REAL
//! `Runtime::apply` post-state root: it includes the bandwidth-scheduler state
//! write (`TrieKey::BandwidthSchedulerState`, key `0x0f`) for a single-shard
//! layout. The context therefore also binds the shard's congestion info
//! (`ExtendedCongestionInfo`: `CongestionInfoV1` + `missed_chunks_count`), and
//! the shard id becomes semantic (it is written into the scheduler state).
//!
//! Formats: `spec/claim-v2.md`. Semantics: `spec/near-transfer-receipt-v2.md`.
//! v1 (`--scope v1`, the default) is untouched: none of its code paths change.

use borsh::BorshDeserialize;
use near_parameters::RuntimeConfigStore;
use near_primitives::apply::ApplyChunkReason;
use near_primitives::bandwidth_scheduler::{BandwidthSchedulerState, BlockBandwidthRequests};
use near_primitives::congestion_info::{
    BlockCongestionInfo, CongestionInfo, CongestionInfoV1, ExtendedCongestionInfo,
};
use near_primitives::hash::{CryptoHash, hash};
use near_primitives::merkle::merklize;
use near_primitives::receipt::{Receipt, ReceiptEnum};
use near_primitives::shard_layout::ShardLayout;
use near_primitives::state::PartialState;
use near_primitives::test_utils::MockEpochInfoProvider;
use near_primitives::transaction::{ExecutionOutcomeWithId, ExecutionStatus};
use near_primitives::trie_key::TrieKey;
use near_primitives::types::{EpochId, Gas, ShardId};
use near_store::ShardTries;
use near_store::test_utils::TestTriesBuilder;
use near_store::trie::AccessOptions;
use node_runtime::{ApplyState, Runtime, SignedValidPeriodTransactions};
use serde_json::json;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::casegen::{self, Rng};
use crate::domain as d1;
use crate::enc::{self, R, W};
use crate::exec::{receipts_commitment, refunds_commitment};

pub const REQUEST_FORMAT: &str = "near-arena-request-v2";
pub const WITNESS_FORMAT: &str = "near-arena-witness-v2";
pub const CLAIM_FORMAT: &str = "near-arena-claim-v2";
pub const PARAMS_FORMAT: &str = "near-arena-params-v1";
pub const STATEMENT_ID: &str = "near/pv86/receipt-transfer-batch/v1";
pub const BW_KEY: [u8; 1] = [0x0f];
/// Domain `single_shard_layout`: the shard id fits `ShardUId`'s u32 field.
pub const MAX_SHARD_ID_EXCL: u64 = 1 << 32;

/// The shard's `ExtendedCongestionInfo` from the block (`apply_state.congestion_info`):
/// `CongestionInfo::V1` of the previous chunk + `missed_chunks_count`.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Congestion {
    pub delayed_receipts_gas: u128,
    pub buffered_receipts_gas: u128,
    pub receipt_bytes: u64,
    pub allowed_shard: u16,
    pub missed_chunks_count: u64,
}

impl Congestion {
    fn write(&self, w: &mut W) {
        w.u128(self.delayed_receipts_gas)
            .u128(self.buffered_receipts_gas)
            .u64(self.receipt_bytes)
            .raw(&self.allowed_shard.to_le_bytes())
            .u64(self.missed_chunks_count);
    }
    fn read(r: &mut R) -> Result<Congestion, String> {
        Ok(Congestion {
            delayed_receipts_gas: r.u128()?,
            buffered_receipts_gas: r.u128()?,
            receipt_bytes: r.u64()?,
            allowed_shard: u16::from_le_bytes(r.take(2)?.try_into().unwrap()),
            missed_chunks_count: r.u64()?,
        })
    }
    fn to_json(&self) -> serde_json::Value {
        json!({
            "delayed_receipts_gas": self.delayed_receipts_gas.to_string(),
            "buffered_receipts_gas": self.buffered_receipts_gas.to_string(),
            "receipt_bytes": self.receipt_bytes,
            "allowed_shard": self.allowed_shard,
            "missed_chunks_count": self.missed_chunks_count,
        })
    }
}

#[derive(Clone, Debug)]
pub struct Request {
    pub protocol_version: u32,
    pub chain_id: String,
    pub shard_id: u64,
    pub block_height: u64,
    pub block_gas_price: u128,
    pub gas_limit: u64,
    pub congestion: Congestion,
    pub pre_state_root: CryptoHash,
    pub receipts: Vec<Receipt>,
}

impl Request {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = W::default();
        w.str(REQUEST_FORMAT)
            .str(STATEMENT_ID)
            .u32(self.protocol_version)
            .str(&self.chain_id)
            .u64(self.shard_id)
            .u64(self.block_height)
            .u128(self.block_gas_price)
            .u64(self.gas_limit);
        self.congestion.write(&mut w);
        w.raw(self.pre_state_root.as_ref()).u32(self.receipts.len().try_into().unwrap());
        for r in &self.receipts {
            w.raw(&borsh::to_vec(r).unwrap());
        }
        w.0
    }

    /// The v1 view (drops the congestion fields) — used to reuse the v1
    /// receipt-level domain predicate unchanged.
    pub fn to_v1(&self) -> enc::Request {
        enc::Request {
            protocol_version: self.protocol_version,
            chain_id: self.chain_id.clone(),
            shard_id: self.shard_id,
            block_height: self.block_height,
            block_gas_price: self.block_gas_price,
            gas_limit: self.gas_limit,
            pre_state_root: self.pre_state_root,
            receipts: self.receipts.clone(),
        }
    }

    pub fn from_v1(r: enc::Request) -> Request {
        Request {
            protocol_version: r.protocol_version,
            chain_id: r.chain_id,
            shard_id: r.shard_id,
            block_height: r.block_height,
            block_gas_price: r.block_gas_price,
            gas_limit: r.gas_limit,
            congestion: Congestion::default(),
            pre_state_root: r.pre_state_root,
            receipts: r.receipts,
        }
    }
}

pub fn decode_request(b: &[u8]) -> Result<Request, String> {
    let mut r = R::new(b);
    r.expect_str(REQUEST_FORMAT)?;
    r.expect_str(STATEMENT_ID)?;
    let protocol_version = r.u32()?;
    let chain = r.bytes()?;
    if !enc::chain_id_ok(chain) {
        return Err("bad chain id".into());
    }
    let shard_id = r.u64()?;
    let block_height = r.u64()?;
    let block_gas_price = r.u128()?;
    let gas_limit = r.u64()?;
    let congestion = Congestion::read(&mut r)?;
    let pre_state_root = CryptoHash(r.h32()?);
    let n = r.u32()?;
    let mut rest = r.rest();
    let mut receipts = vec![];
    for _ in 0..n {
        receipts.push(Receipt::deserialize(&mut rest).map_err(|e| format!("receipt: {e}"))?);
    }
    if !rest.is_empty() {
        return Err("trailing bytes after receipts".into());
    }
    Ok(Request {
        protocol_version,
        chain_id: String::from_utf8(chain.to_vec()).unwrap(),
        shard_id,
        block_height,
        block_gas_price,
        gas_limit,
        congestion,
        pre_state_root,
        receipts,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub protocol_version: u32,
    pub chain_id: String,
    pub shard_id: u64,
    pub block_height: u64,
    pub block_gas_price: u128,
    pub gas_limit: u64,
    pub congestion: Congestion,
    pub pre_state_root: [u8; 32],
    pub receipt_count: u32,
    pub receipts_commitment: [u8; 32],
    pub post_state_root: [u8; 32],
    pub outcome_root: [u8; 32],
    pub refund_count: u32,
    pub refund_receipts_commitment: [u8; 32],
    pub gas_burnt_total: u64,
    pub tokens_burnt_total: u128,
}

impl Claim {
    pub fn encode(&self) -> Vec<u8> {
        let mut w = W::default();
        w.str(CLAIM_FORMAT)
            .str(STATEMENT_ID)
            .u32(self.protocol_version)
            .str(&self.chain_id)
            .u64(self.shard_id)
            .u64(self.block_height)
            .u128(self.block_gas_price)
            .u64(self.gas_limit);
        self.congestion.write(&mut w);
        w.raw(&self.pre_state_root)
            .u32(self.receipt_count)
            .raw(&self.receipts_commitment)
            .raw(&self.post_state_root)
            .raw(&self.outcome_root)
            .u32(self.refund_count)
            .raw(&self.refund_receipts_commitment)
            .u64(self.gas_burnt_total)
            .u128(self.tokens_burnt_total);
        w.0
    }

    pub fn decode(b: &[u8]) -> Result<Claim, String> {
        let mut r = R::new(b);
        r.expect_str(CLAIM_FORMAT)?;
        r.expect_str(STATEMENT_ID)?;
        let protocol_version = r.u32()?;
        let chain = r.bytes()?;
        if !enc::chain_id_ok(chain) {
            return Err("bad chain id".into());
        }
        let c = Claim {
            protocol_version,
            chain_id: String::from_utf8(chain.to_vec()).unwrap(),
            shard_id: r.u64()?,
            block_height: r.u64()?,
            block_gas_price: r.u128()?,
            gas_limit: r.u64()?,
            congestion: Congestion::read(&mut r)?,
            pre_state_root: r.h32()?,
            receipt_count: r.u32()?,
            receipts_commitment: r.h32()?,
            post_state_root: r.h32()?,
            outcome_root: r.h32()?,
            refund_count: r.u32()?,
            refund_receipts_commitment: r.h32()?,
            gas_burnt_total: r.u64()?,
            tokens_burnt_total: r.u128()?,
        };
        r.end()?;
        Ok(c)
    }

    pub fn to_json(&self) -> serde_json::Value {
        json!({
            "protocol_version": self.protocol_version,
            "chain_id": self.chain_id,
            "shard_id": self.shard_id,
            "block_height": self.block_height,
            "block_gas_price": self.block_gas_price.to_string(),
            "gas_limit": self.gas_limit,
            "congestion": self.congestion.to_json(),
            "pre_state_root": hex::encode(self.pre_state_root),
            "receipt_count": self.receipt_count,
            "receipts_commitment": hex::encode(self.receipts_commitment),
            "post_state_root": hex::encode(self.post_state_root),
            "outcome_root": hex::encode(self.outcome_root),
            "refund_count": self.refund_count,
            "refund_receipts_commitment": hex::encode(self.refund_receipts_commitment),
            "gas_burnt_total": self.gas_burnt_total,
            "tokens_burnt_total": self.tokens_burnt_total.to_string(),
        })
    }
}

/// witness.bin (v2): same layout as v1 under the `near-arena-witness-v2` tag;
/// the values cover the receivers' Account paths AND the path to `0x0f`.
pub fn encode_witness(pre_root: &CryptoHash, values: &[Vec<u8>]) -> Vec<u8> {
    let mut sorted = values.to_vec();
    sorted.sort();
    sorted.dedup();
    let mut w = W::default();
    w.str(WITNESS_FORMAT).raw(pre_root.as_ref()).u8(0).u32(sorted.len().try_into().unwrap());
    for v in &sorted {
        w.bytes(v);
    }
    w.0
}

// ---------------------------------------------------------------- domain

/// v2 domain: every v1 restriction (receipt-level, reused verbatim) plus the
/// scheduler-context restrictions. Re-implemented without nearcore runtime code.
pub fn check(req: &Request, kv: &BTreeMap<Vec<u8>, Vec<u8>>, witness_bytes: usize) -> Result<d1::Sim, String> {
    let sim = d1::check(&req.to_v1(), kv, witness_bytes)?;
    if req.shard_id >= MAX_SHARD_ID_EXCL {
        return Err("shard_id >= 2^32".into());
    }
    let c = &req.congestion;
    if c.delayed_receipts_gas != 0 || c.buffered_receipts_gas != 0 || c.receipt_bytes != 0 {
        return Err("congestion info not zero (delayed/buffered gas, receipt bytes)".into());
    }
    if let Some(v) = kv.get(&BW_KEY.to_vec()) {
        if BandwidthSchedulerState::try_from_slice(v).is_err() {
            return Err("bandwidth scheduler state in pre-state does not decode".into());
        }
    }
    if c.missed_chunks_count > 0 && sim.refunds > 0 {
        return Err("gas refund with missed_chunks_count > 0 (no bandwidth granted: refund would be buffered)".into());
    }
    Ok(sim)
}

// ---------------------------------------------------------------- exec

pub struct Executed {
    pub request: Request,
    pub claim: Option<Claim>,
    pub witness_values: Vec<Vec<u8>>,
    pub nearcore: serde_json::Value,
    pub clean: bool,
    pub problems: Vec<String>,
}

fn h(x: &CryptoHash) -> String {
    hex::encode(x.as_ref())
}

fn fail(req: Request, wv: Vec<Vec<u8>>, nearcore: serde_json::Value, p: String) -> Executed {
    Executed { request: req, claim: None, witness_values: wv, nearcore, clean: false, problems: vec![p] }
}

/// Run the real `Runtime::apply` for a single-shard layout whose only shard is
/// `req.shard_id`, with the request's congestion info, and derive the v2 claim.
pub fn run(mut req: Request, state: &BTreeMap<Vec<u8>, Vec<u8>>) -> Executed {
    let mut problems = vec![];
    let config_store = RuntimeConfigStore::new(None);
    let config = config_store.get_config(req.protocol_version).clone();

    let shard_id = ShardId::new(req.shard_id);
    let shard_layout = ShardLayout::v2(vec![], vec![shard_id], None);
    let epoch_info_provider = MockEpochInfoProvider::new(shard_layout.clone());
    let shard_uid = shard_layout.shard_uids().next().unwrap();
    if shard_uid.shard_id() != shard_id {
        problems.push(format!("ShardUId cannot represent shard id {}", req.shard_id));
    }

    let tries: ShardTries = TestTriesBuilder::new().build();
    let empty = tries.get_trie_for_shard(shard_uid, CryptoHash::default());
    let changes: Vec<(Vec<u8>, Option<Vec<u8>>)> =
        state.iter().map(|(k, v)| (k.clone(), Some(v.clone()))).collect();
    let tc = empty.update(changes, AccessOptions::DEFAULT).unwrap();
    let mut su = tries.store_update();
    let pre_root = tries.apply_all(&tc, shard_uid, &mut su);
    su.commit();
    req.pre_state_root = pre_root;

    let c = &req.congestion;
    let ext = ExtendedCongestionInfo::new(
        CongestionInfo::V1(CongestionInfoV1 {
            delayed_receipts_gas: c.delayed_receipts_gas,
            buffered_receipts_gas: c.buffered_receipts_gas,
            receipt_bytes: c.receipt_bytes,
            allowed_shard: c.allowed_shard,
        }),
        c.missed_chunks_count,
    );
    let apply_state = ApplyState {
        apply_reason: ApplyChunkReason::UpdateTrackedShard,
        block_height: req.block_height,
        prev_block_hash: CryptoHash::default(),
        shard_id,
        epoch_id: EpochId::default(),
        epoch_height: 0,
        gas_price: near_primitives::types::Balance::from_yoctonear(req.block_gas_price),
        block_timestamp: 1_000,
        gas_limit: Some(Gas::from_gas(req.gas_limit)),
        random_seed: CryptoHash::default(),
        current_protocol_version: req.protocol_version,
        config: config.clone(),
        next_wasm_config: None,
        cache: None,
        trie_access_tracker_state: Default::default(),
        is_new_chunk: true,
        save_receipt_to_tx: false,
        congestion_info: BlockCongestionInfo::new([(shard_id, ext)].into_iter().collect()),
        bandwidth_requests: BlockBandwidthRequests::empty(),
        on_post_state_ready: None,
    };

    // Slice witness: nearcore's TrieRecorder over reads of every receiver's
    // Account key and of the bandwidth-scheduler key on the pre-state trie.
    let rec = tries.get_trie_for_shard(shard_uid, pre_root).recording_reads_new_recorder();
    for r in &req.receipts {
        let _ = rec.get(&d1::account_key(r.receiver_id().as_str()), AccessOptions::DEFAULT).unwrap();
    }
    let bw_before = rec.get(&TrieKey::BandwidthSchedulerState.to_vec(), AccessOptions::DEFAULT).unwrap();
    let proof = rec.recorded_storage().unwrap();
    let PartialState::TrieValues(values) = &proof.nodes;
    let witness_values: Vec<Vec<u8>> = values.iter().map(|v| v.to_vec()).collect();

    let trie = tries.get_trie_for_shard(shard_uid, pre_root).recording_reads_new_recorder();
    let t0 = std::time::Instant::now();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        Runtime::new().apply(
            trie,
            &None,
            &apply_state,
            &req.receipts,
            SignedValidPeriodTransactions::empty(),
            &epoch_info_provider,
            Default::default(),
        )
    }));
    let apply_ns = t0.elapsed().as_nanos() as u64;
    let result = match res {
        Err(_) => {
            let j = json!({"apply": "panicked", "apply_ns": apply_ns});
            return fail(req, witness_values, j, "Runtime::apply panicked".into());
        }
        Ok(Err(e)) => {
            let j = json!({"apply": "error", "error": format!("{e:?}"), "apply_ns": apply_ns});
            return fail(req, witness_values, j, format!("Runtime::apply error: {e:?}"));
        }
        Ok(Ok(r)) => r,
    };

    let n = req.receipts.len();
    if result.outcomes.len() != n {
        problems.push(format!("{} outcomes for {} receipts", result.outcomes.len(), n));
    }
    if result.delayed_receipts_count != 0 {
        problems.push(format!("{} delayed receipts", result.delayed_receipts_count));
    }
    let mut statuses = BTreeMap::<String, usize>::new();
    for (o, r) in result.outcomes.iter().zip(req.receipts.iter()) {
        if o.id != *r.receipt_id() {
            problems.push("outcome order != receipt order".into());
        }
        let s = match &o.outcome.status {
            ExecutionStatus::SuccessValue(v) if v.is_empty() => "SuccessValue([])".to_string(),
            s => {
                problems.push(format!("receipt {} status {:?}", h(&o.id), s));
                format!("{s:?}")
            }
        };
        *statuses.entry(s).or_default() += 1;
        if !o.outcome.logs.is_empty() {
            problems.push("logs not empty".into());
        }
    }
    let hashes: Vec<Vec<CryptoHash>> = result.outcomes.iter().map(ExecutionOutcomeWithId::to_hashes).collect();
    let (outcome_root, _) = merklize(&hashes);
    let refund_ids: Vec<CryptoHash> =
        result.outcomes.iter().flat_map(|o| o.outcome.receipt_ids.iter().cloned()).collect();
    let out_ids: Vec<CryptoHash> = result.outgoing_receipts.iter().map(|r| *r.receipt_id()).collect();
    if refund_ids != out_ids {
        problems.push(format!(
            "outgoing receipts ({}) != outcome receipt_ids ({}) (buffered?)",
            out_ids.len(),
            refund_ids.len()
        ));
    }
    let gas_total: u64 = result.outcomes.iter().map(|o| o.outcome.gas_burnt.as_gas()).sum();
    let tokens_total: u128 = result.outcomes.iter().map(|o| o.outcome.tokens_burnt.as_yoctonear()).sum();
    if tokens_total != result.stats.balance.tx_burnt_amount.as_yoctonear() {
        problems.push("sum(tokens_burnt) != stats.balance.tx_burnt_amount".into());
    }
    let b = &result.stats.balance;
    if !b.other_burnt_amount.is_zero() || !b.gas_deficit_amount.is_zero() || !b.slashed_burnt_amount.is_zero() {
        problems.push(format!("unexpected balance stats {b:?}"));
    }

    let all: Vec<(Vec<u8>, Option<Vec<u8>>)> = result
        .state_changes
        .iter()
        .map(|ch| (ch.trie_key.to_vec(), ch.changes.last().unwrap().data.clone()))
        .collect();
    let mut bw_after: Option<Vec<u8>> = None;
    for (k, v) in &all {
        if k[0] == 0 {
            match v {
                None => problems.push("account deleted".into()),
                Some(v) if v.len() != 72 => problems.push("account value length changed".into()),
                _ => {}
            }
            if !state.contains_key(k) {
                problems.push("account key inserted".into());
            }
        } else if k.as_slice() == BW_KEY {
            match v {
                None => problems.push("bandwidth scheduler state deleted".into()),
                Some(v) => bw_after = Some(v.clone()),
            }
        } else {
            problems.push(format!("unexpected key changed: {}", hex::encode(k)));
        }
    }
    if bw_after.is_none() {
        problems.push("bandwidth scheduler state not written".into());
    }
    let base = tries.get_trie_for_shard(shard_uid, pre_root);
    let full_again = base.update(all.clone(), AccessOptions::DEFAULT).unwrap().new_root;
    let decomposition_ok = full_again == result.state_root;
    if !decomposition_ok {
        problems.push("decomposition failed: pre ⊕ changes != Runtime::apply root".into());
    }
    // Witness-only re-execution: the recorded slice witness suffices for nearcore
    // itself to compute the full post-state root (incl. the 0x0f insert/update).
    let wt = near_store::Trie::from_recorded_storage(proof.clone(), pre_root, false);
    let witness_root = match wt.update(all.clone(), AccessOptions::DEFAULT) {
        Ok(u) => Some(u.new_root),
        Err(e) => {
            problems.push(format!("witness-only update failed: {e:?}"));
            None
        }
    };
    if witness_root.is_some() && witness_root != Some(result.state_root) {
        problems.push("witness-only post root mismatch".into());
    }
    let full_recorded = result.proof.as_ref().map(|p| {
        let PartialState::TrieValues(v) = &p.nodes;
        v.iter().map(|x| x.len()).sum::<usize>()
    });
    let bw_after_decoded = bw_after.as_ref().and_then(|v| BandwidthSchedulerState::try_from_slice(v).ok()).map(|s| {
        let BandwidthSchedulerState::V1(s) = s;
        json!({
            "link_allowances": s.link_allowances.iter().map(|l| json!([l.sender.to_string(), l.receiver.to_string(), l.allowance])).collect::<Vec<_>>(),
            "sanity_check_hash": h(&s.sanity_check_hash),
        })
    });

    let claim = Claim {
        protocol_version: req.protocol_version,
        chain_id: req.chain_id.clone(),
        shard_id: req.shard_id,
        block_height: req.block_height,
        block_gas_price: req.block_gas_price,
        gas_limit: req.gas_limit,
        congestion: req.congestion.clone(),
        pre_state_root: pre_root.0,
        receipt_count: n as u32,
        receipts_commitment: receipts_commitment(req.shard_id, &req.receipts),
        post_state_root: result.state_root.0,
        outcome_root: outcome_root.0,
        refund_count: result.outgoing_receipts.len() as u32,
        refund_receipts_commitment: refunds_commitment(&result.outgoing_receipts),
        gas_burnt_total: gas_total,
        tokens_burnt_total: tokens_total,
    };
    let nearcore = json!({
        "apply": "ok",
        "apply_ns": apply_ns,
        "post_state_root": h(&result.state_root),
        "decomposition_ok": decomposition_ok,
        "witness_only_post_root_ok": witness_root == Some(result.state_root),
        "bandwidth_state_before": bw_before.as_ref().map(|v| hex::encode(&v[..])),
        "bandwidth_state_after": bw_after.as_ref().map(hex::encode),
        "bandwidth_state_after_decoded": bw_after_decoded,
        "keys_changed": all.len(),
        "outcome_statuses": statuses,
        "outgoing_receipts": result.outgoing_receipts.len(),
        "delayed_receipts_count": result.delayed_receipts_count,
        "tx_burnt_amount": result.stats.balance.tx_burnt_amount.as_yoctonear().to_string(),
        "full_apply_recorded_bytes": full_recorded,
        "slice_witness_values": witness_values.len(),
        "slice_witness_bytes": witness_values.iter().map(|v| v.len()).sum::<usize>(),
    });
    let clean = problems.is_empty();
    Executed { request: req, claim: Some(claim), witness_values, nearcore, clean, problems }
}

// ---------------------------------------------------------------- generator

pub struct Case {
    pub id: String,
    pub profile: String,
    pub request: Request,
    pub state: BTreeMap<Vec<u8>, Vec<u8>>,
    pub invalid_kind: Option<String>,
}

/// v1 profiles (receipt/state shapes) plus v2-specific ones:
/// `bw_state` (varied pre-existing scheduler states), `trie_shapes` (states that
/// force every insert case: root leaf/extension/branch, exotic keys under 0x0f),
/// `missed` (missed_chunks_count > 0, no refunds), `shards` (non-zero shard ids).
pub const PROFILES: &[&str] = &[
    "basic", "prefix", "boundary", "repeat", "prices", "large", "bw_state", "trie_shapes", "missed", "shards",
];

pub const INVALID_KINDS: &[&str] = &[
    // v1 families (receipt level), re-checked under v2
    "receiver_missing",
    "balance_overflow",
    "sentinel_balance",
    "storage_stake",
    "implicit_receiver",
    "system_predecessor",
    "multi_action",
    "non_transfer_action",
    "gas_limit",
    "duplicate_receipt_id",
    "account_v2",
    "tokens_burnt_overflow",
    "wrong_protocol_version",
    "empty_batch",
    // v2 context families
    "bw_state_undecodable",
    "nonzero_congestion",
    "missed_chunk_refund",
    "shard_id_too_large",
];

fn bw_value(links: &[(u64, u64, u64)], hash32: [u8; 32]) -> Vec<u8> {
    let mut w = W::default();
    w.u8(0).u32(links.len() as u32);
    for (s, r, a) in links {
        w.u64(*s).u64(*r).u64(*a);
    }
    w.raw(&hash32);
    w.0
}

fn pick_shard_id(rng: &mut Rng, wide: bool) -> u64 {
    if wide {
        let r = rng.below(1 << 32);
        *rng.pick(&[0u64, 1, 2, 5, 7, 15, 255, 65535, 65536, 1 << 31, (1u64 << 32) - 1, r])
    } else if rng.chance(3, 4) {
        0
    } else {
        rng.range(1, 20)
    }
}

fn random_bw_state(rng: &mut Rng, shard: u64) -> Option<Vec<u8>> {
    match rng.below(6) {
        0 => None,
        1 | 2 => {
            // what a single-shard chain actually stores: one (S,S) link
            let r = rng.below(4_500_001);
            let a = *rng.pick(&[4_400_000u64, 4_500_000, r]);
            Some(bw_value(&[(shard, shard, a)], rng.bytes32()))
        }
        3 => Some(bw_value(&[], rng.bytes32())),
        4 => {
            // stale multi-shard state (e.g. a previous layout), arbitrary allowances
            let k = rng.range(1, 6) as usize;
            let links: Vec<(u64, u64, u64)> = (0..k)
                .map(|_| {
                    let s = if rng.chance(1, 3) { shard } else { rng.below(10) };
                    let r = if rng.chance(1, 3) { shard } else { rng.below(10) };
                    let x = rng.next();
                    (s, r, *rng.pick(&[0u64, u64::MAX, x, 4_500_000]))
                })
                .collect();
            Some(bw_value(&links, rng.bytes32()))
        }
        _ => Some(bw_value(&[(shard, shard, 4_400_000)], [0u8; 32])),
    }
}

/// Reshape the state so that the 0x0f insert/update hits a particular trie case
/// (each `PTrie.upsert` branch: leaf split with/without the new key ending at the
/// branch, extension split with/without, new branch child, branch value).
fn reshape_state(rng: &mut Rng, case: &mut casegen::Case) {
    let exotic = |rng: &mut Rng, first: Option<u8>| -> Vec<u8> {
        let mut k = vec![0x0fu8, first.unwrap_or(rng.next() as u8)];
        k.extend((0..rng.range(0, 2)).map(|_| rng.next() as u8));
        k
    };
    let single_receiver = |case: &mut casegen::Case| {
        let keep = case.request.receipts[0].receiver_id().clone();
        case.request.receipts.retain(|r| *r.receiver_id() == keep);
        let k = d1::account_key(keep.as_str());
        case.state.retain(|kk, _| *kk == k);
    };
    match rng.below(8) {
        // accounts only: every key starts with nibbles 0,0 -> root extension split
        0 => case.state.retain(|k, _| k[0] == 0),
        // one key: root leaf -> leaf split, both keys continue past the branch
        1 => single_receiver(case),
        // one account + one 0x0f.. key: the new key ends where the old leaf continues
        2 => {
            single_receiver(case);
            let k = exotic(rng, None);
            case.state.insert(k, vec![1, 2, 3]);
        }
        // >= 2 keys diverging right after 0x0f: 0x0f is a branch -> branch value
        3 => {
            let a = rng.next() as u8;
            let b = a ^ 0x80;
            case.state.insert(exotic(rng, Some(a)), vec![4; 9]);
            case.state.insert(exotic(rng, Some(b)), vec![5; 2]);
        }
        // 2 keys sharing the next nibble: extension below 0x0f -> ext split, key ends
        4 => {
            let a = rng.next() as u8;
            case.state.insert(vec![0x0f, a, 1], vec![6; 3]);
            case.state.insert(vec![0x0f, a, 0x81], vec![6; 4]);
        }
        // keys in high columns (first nibble 1): root branch at depth 0
        5 => {
            for _ in 0..rng.range(1, 4) {
                let col = *rng.pick(&[0x12u8, 0x13, 0x14, 0x16, 0x17]);
                let mut k = vec![col];
                k.extend((0..rng.range(1, 12)).map(|_| rng.next() as u8));
                let v: Vec<u8> = (0..rng.range(0, 64)).map(|_| rng.next() as u8).collect();
                case.state.insert(k, v);
            }
        }
        // one account + one high-column key: root branch, new child at nibble 0
        6 => {
            single_receiver(case);
            case.state.insert(vec![0x13, rng.next() as u8], vec![1]);
        }
        // nibble-0x0 columns next to 0x0f (code 0x01, contract data 0x09, 0x0e)
        _ => {
            let ids: Vec<String> = case.request.receipts.iter().map(|r| r.receiver_id().to_string()).collect();
            for id in ids.iter().take(3) {
                let mut k = vec![*rng.pick(&[0x01u8, 0x09, 0x0e])];
                k.extend_from_slice(id.as_bytes());
                k.push(b',');
                k.push(rng.next() as u8);
                case.state.insert(k, vec![7; rng.range(0, 20) as usize]);
            }
        }
    }
}

fn no_refunds(req: &Request) -> bool {
    req.receipts.iter().all(|r| {
        let Receipt::V0(v0) = r;
        let ReceiptEnum::Action(a) = &v0.receipt else { return true };
        a.gas_price.as_yoctonear() <= req.block_gas_price
    })
}

fn force_no_refunds(req: &mut Request) {
    let mx = req
        .receipts
        .iter()
        .map(|r| {
            let Receipt::V0(v0) = r;
            match &v0.receipt {
                ReceiptEnum::Action(a) => a.gas_price.as_yoctonear(),
                _ => 0,
            }
        })
        .max()
        .unwrap_or(0);
    req.block_gas_price = req.block_gas_price.max(mx);
}

pub fn gen_valid(seed: u64, idx: u64, profile: &str) -> Case {
    let v1_profile = if casegen::PROFILES.contains(&profile) { profile } else { "basic" };
    for attempt in 0u64.. {
        let mut base = casegen::gen_valid(seed, idx.wrapping_mul(7).wrapping_add(attempt), v1_profile);
        let mut rng = Rng::new(seed ^ 0xB4D5_C0DE_0000_0002, idx.wrapping_mul(1000).wrapping_add(attempt));
        if profile == "trie_shapes" {
            reshape_state(&mut rng, &mut base);
        }
        let mut req = Request::from_v1(base.request);
        req.shard_id = pick_shard_id(&mut rng, profile == "shards");
        req.congestion.allowed_shard = if rng.chance(3, 4) { req.shard_id as u16 } else { rng.next() as u16 };
        let missed = match profile {
            "missed" => {
                let x = rng.next() >> 1;
                *rng.pick(&[1u64, 1, 2, 3, 10, 124, 125, 126, 1000, x])
            }
            _ if rng.chance(1, 30) => rng.range(1, 5),
            _ => 0,
        };
        if missed > 0 {
            force_no_refunds(&mut req);
            if no_refunds(&req) {
                req.congestion.missed_chunks_count = missed;
            }
        }
        let bw = match profile {
            "bw_state" => random_bw_state(&mut rng, req.shard_id),
            "trie_shapes" if rng.chance(2, 3) => None,
            "trie_shapes" => random_bw_state(&mut rng, req.shard_id),
            _ if rng.chance(1, 3) => None,
            _ => Some(bw_value(&[(req.shard_id, req.shard_id, 4_400_000)], rng.bytes32())),
        };
        let mut state = base.state;
        match bw {
            Some(v) => {
                state.insert(BW_KEY.to_vec(), v);
            }
            None => {
                state.remove(&BW_KEY.to_vec());
            }
        }
        if check(&req, &state, 0).is_ok() {
            let id = format!("s{seed}-w{idx}");
            return Case { id, profile: profile.into(), request: req, state, invalid_kind: None };
        }
    }
    unreachable!()
}

pub fn gen_invalid(seed: u64, idx: u64, kind: &str) -> Case {
    let mut rng = Rng::new(seed ^ 0xB4D5_BAD0_0000_0002, idx);
    if casegen::INVALID_KINDS.contains(&kind) {
        let c = casegen::gen_invalid(seed, idx, kind);
        let mut req = Request::from_v1(c.request);
        req.shard_id = pick_shard_id(&mut rng, false);
        req.congestion.allowed_shard = req.shard_id as u16;
        let mut state = c.state;
        if rng.chance(1, 2) {
            state.insert(BW_KEY.to_vec(), bw_value(&[(req.shard_id, req.shard_id, 4_400_000)], rng.bytes32()));
        }
        return Case { id: format!("s{seed}-y{idx}-{kind}"), profile: "invalid".into(), request: req, state, invalid_kind: Some(kind.into()) };
    }
    let mut c = gen_valid(seed, idx, *rng.pick(&["basic", "prices", "bw_state"]));
    c.id = format!("s{seed}-y{idx}-{kind}");
    c.invalid_kind = Some(kind.into());
    match kind {
        "bw_state_undecodable" => {
            let good = bw_value(&[(c.request.shard_id, c.request.shard_id, 4_400_000)], rng.bytes32());
            let bad = match rng.below(5) {
                0 => {
                    let mut v = good;
                    v[0] = 1; // unknown enum tag
                    v
                }
                1 => {
                    let mut v = good;
                    v.push(0); // trailing byte
                    v
                }
                2 => good[..good.len() - 1].to_vec(), // truncated hash
                3 => {
                    let mut v = good;
                    v[1] = 2; // link count larger than the data
                    v
                }
                _ => vec![],
            };
            c.state.insert(BW_KEY.to_vec(), bad);
        }
        // Only delayed gas / receipt bytes: a non-zero buffered_receipts_gas with
        // empty outgoing buffers violates a nearcore invariant and makes
        // Runtime::apply panic (congestion_control.rs:281-284) — such an input
        // cannot come from a real chain.
        "nonzero_congestion" => match rng.below(2) {
            0 => c.request.congestion.delayed_receipts_gas = 1 + rng.u128_below(1u128 << 70),
            _ => c.request.congestion.receipt_bytes = 1 + rng.below(1 << 30),
        },
        "missed_chunk_refund" => {
            // at least one receipt pays more than the block price
            let p = c.request.block_gas_price;
            let Receipt::V0(v0) = &mut c.request.receipts[0];
            if let ReceiptEnum::Action(a) = &mut v0.receipt {
                a.gas_price = near_primitives::types::Balance::from_yoctonear(p + 1);
            }
            c.request.congestion.missed_chunks_count = rng.range(1, 3);
        }
        "shard_id_too_large" => {
            c.request.shard_id = (1u64 << 32) + rng.below(1 << 20);
            c.request.congestion.allowed_shard = 0;
            if c.state.contains_key(&BW_KEY.to_vec()) {
                c.state.insert(BW_KEY.to_vec(), bw_value(&[], [0; 32]));
            }
        }
        other => panic!("unknown invalid kind {other}"),
    }
    c
}

/// The v1 worked example (alice/bob/carol) under v2: shard 0, zero congestion,
/// `bw` = None (state absent: insert) or Some (a realistic previous state: update).
pub fn example_case(tier: &str, with_prev_bw: bool) -> Case {
    let base = casegen::example_case(tier);
    let mut req = Request::from_v1(base.request);
    req.congestion.allowed_shard = 0;
    let mut state = base.state;
    let mut id = format!("example-v2-tier{tier}");
    if with_prev_bw {
        // the state nearcore itself writes after one chunk at this layout
        // (prev hash = sha256(0^32 ‖ sha256(u32 1 ‖ u64 0)))
        let mut x = vec![0u8; 32];
        x.extend_from_slice(&hash(&[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).0);
        state.insert(BW_KEY.to_vec(), bw_value(&[(0, 0, 4_400_000)], hash(&x).0));
        id.push_str("-bw");
    }
    Case { id, profile: "example".into(), request: req, state, invalid_kind: None }
}

// ---------------------------------------------------------------- commands

pub struct Layout {
    pub claim_name: &'static str,
}

pub fn write_case(dir: &Path, case: &Case, ex: &Executed, seed: u64, idx: u64, layout: &Layout) -> bool {
    std::fs::create_dir_all(dir).unwrap();
    let req_bytes = ex.request.encode();
    let witness = encode_witness(&ex.request.pre_state_root, &ex.witness_values);
    let kv: Vec<(Vec<u8>, Vec<u8>)> = case.state.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    std::fs::write(dir.join("request.bin"), &req_bytes).unwrap();
    std::fs::write(dir.join("witness.bin"), &witness).unwrap();
    std::fs::write(dir.join("state.bin"), enc::encode_state(&kv)).unwrap();
    let wbytes: usize = ex.witness_values.iter().map(|v| v.len()).sum();
    let dom = check(&ex.request, &case.state, wbytes);
    let in_domain = dom.is_ok();
    let expected_in_domain = case.invalid_kind.is_none();
    let mut consistent = in_domain == expected_in_domain;
    if in_domain && !ex.clean {
        consistent = false;
    }
    if in_domain {
        let c = ex.claim.as_ref().unwrap();
        std::fs::write(dir.join(layout.claim_name), c.encode()).unwrap();
        assert_eq!(Claim::decode(&c.encode()).unwrap(), *c);
        assert!(decode_request(&req_bytes).is_ok());
        if let Ok(sim) = &dom {
            if sim.tokens_burnt_total != c.tokens_burnt_total || sim.refunds as u32 != c.refund_count {
                consistent = false;
            }
        }
    } else {
        let _ = std::fs::remove_file(dir.join(layout.claim_name));
    }
    let diag = json!({
        "schema": "near-arena-oracle-case-v2",
        "scope": "v2",
        "statement_id": STATEMENT_ID,
        "case_id": case.id,
        "generator": {"seed": seed, "index": idx, "profile": case.profile, "invalid_kind": case.invalid_kind},
        "nearcore_commit": crate::NEARCORE_COMMIT,
        "synthetic_state": true,
        "in_domain": in_domain,
        "domain_reason": dom.as_ref().err(),
        "expected_in_domain": expected_in_domain,
        "consistent": consistent,
        "nearcore": ex.nearcore,
        "nearcore_problems": ex.problems,
        "claim": ex.claim.as_ref().filter(|_| in_domain).map(|c| c.to_json()),
        "sizes": {
            "request_bytes": req_bytes.len(),
            "witness_bytes": witness.len(),
            "receipts": ex.request.receipts.len(),
            "state_entries": kv.len(),
        },
        "digests": {
            "request.bin": format!("sha256:{}", hex::encode(hash(&req_bytes).0)),
            "witness.bin": format!("sha256:{}", hex::encode(hash(&witness).0)),
            "claim.bin": ex.claim.as_ref().filter(|_| in_domain).map(|c| format!("sha256:{}", hex::encode(hash(&c.encode()).0))),
        }
    });
    std::fs::write(dir.join("diagnostics.json"), serde_json::to_string_pretty(&diag).unwrap() + "\n").unwrap();
    if !consistent {
        eprintln!(
            "INCONSISTENT case {}: in_domain={in_domain} expected={expected_in_domain} reason={:?} problems={:?}",
            case.id,
            dom.as_ref().err(),
            ex.problems
        );
    }
    consistent
}

fn arg(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

pub fn params_bin(runtime_config_digest: &[u8; 32]) -> Vec<u8> {
    let mut w = W::default();
    w.str(PARAMS_FORMAT)
        .str(STATEMENT_ID)
        .u32(d1::PROTOCOL_VERSION)
        .str(d1::CHAIN_ID)
        .raw(runtime_config_digest);
    w.0
}

pub fn cmd_gen(args: &[String]) -> i32 {
    let seed: u64 = arg(args, "--seed").unwrap_or("1".into()).parse().unwrap();
    let nvalid: u64 = arg(args, "--valid").unwrap_or("10".into()).parse().unwrap();
    let ninvalid: u64 = arg(args, "--invalid").unwrap_or("0".into()).parse().unwrap();
    let out = PathBuf::from(arg(args, "--out").expect("--out"));
    let profiles: Vec<String> = arg(args, "--profiles")
        .map(|s| s.split(',').map(String::from).collect())
        .unwrap_or_else(|| PROFILES.iter().map(|s| s.to_string()).collect());
    if let Some(r) = arg(args, "--receipts") {
        let r: usize = r.parse().expect("--receipts N");
        assert!((1..=d1::MAX_BATCH).contains(&r), "--receipts must be in 1..=256");
        casegen::FORCE_RECEIPTS.store(r, std::sync::atomic::Ordering::Relaxed);
    }
    let fixtures = args.iter().any(|a| a == "--fixtures-layout");
    let layout = Layout { claim_name: if fixtures { "expected_claim.bin" } else { "claim.bin" } };
    let case_root = if fixtures { out.join("cases") } else { out.clone() };
    let mut ok = true;
    let mut n = 0u64;
    let mut n_ok = 0u64;
    let t0 = std::time::Instant::now();
    let mut emit = |case: Case, seed: u64, idx: u64| {
        let ex = run(case.request.clone(), &case.state);
        let good = write_case(&case_root.join(&case.id), &case, &ex, seed, idx, &layout);
        ok &= good;
        n += 1;
        n_ok += good as u64;
    };
    if args.iter().any(|a| a == "--with-example") {
        for tier in ["A", "B"] {
            for prev in [false, true] {
                emit(example_case(tier, prev), 0, 0);
            }
        }
        // previous chunk missing: link (0,0) not allowed, allowance stays 4_500_000
        let mut m = example_case("A", true);
        m.id = "example-v2-tierA-bw-missed".into();
        m.request.congestion.missed_chunks_count = 1;
        emit(m, 0, 0);
    }
    for i in 0..nvalid {
        let profile = &profiles[(i as usize) % profiles.len()];
        emit(gen_valid(seed, i, profile), seed, i);
    }
    for i in 0..ninvalid {
        let kind = INVALID_KINDS[(i as usize) % INVALID_KINDS.len()];
        emit(gen_invalid(seed, i, kind), seed, i);
    }
    if fixtures {
        let rc = runtime_config_json();
        let d = hash(crate::jcs(&rc).as_bytes()).0;
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join("params.bin"), params_bin(&d)).unwrap();
    }
    eprintln!("generated {n} v2 cases ({n_ok} consistent) in {:?}", t0.elapsed());
    if ok { 0 } else { 1 }
}

pub fn cmd_replay(args: &[String]) -> i32 {
    let dir = PathBuf::from(arg(args, "--case").expect("--case"));
    let req = decode_request(&std::fs::read(dir.join("request.bin")).unwrap()).unwrap();
    let kv: BTreeMap<Vec<u8>, Vec<u8>> =
        enc::decode_state(&std::fs::read(dir.join("state.bin")).unwrap()).unwrap().into_iter().collect();
    let want_root = req.pre_state_root;
    let ex = run(req, &kv);
    let mut ok = ex.request.pre_state_root == want_root;
    let w = encode_witness(&ex.request.pre_state_root, &ex.witness_values);
    ok &= w == std::fs::read(dir.join("witness.bin")).unwrap();
    let claim_file = if dir.join("claim.bin").exists() { "claim.bin" } else { "expected_claim.bin" };
    match std::fs::read(dir.join(claim_file)) {
        Ok(cb) => ok &= ex.clean && ex.claim.map(|c| c.encode()) == Some(cb),
        Err(_) => {
            let wb: usize = ex.witness_values.iter().map(|v| v.len()).sum();
            ok &= check(&ex.request, &kv, wb).is_err();
        }
    }
    println!("{} {}", if ok { "REPLAY_OK" } else { "REPLAY_MISMATCH" }, dir.display());
    if ok { 0 } else { 1 }
}

/// Runtime-config description for v2: the v1 description plus every
/// bandwidth-scheduler / congestion parameter the v2 relation uses, read from
/// the live config and asserted equal to `NearSpec.Bandwidth`.
pub fn runtime_config_json() -> serde_json::Value {
    let mut d = crate::runtime_config_json();
    let store = RuntimeConfigStore::new(None);
    let cfg = store.get_config(d1::PROTOCOL_VERSION);
    let bw = cfg.bandwidth_scheduler_config;
    let max_receipt_size = cfg.wasm_config.limit_config.max_receipt_size;
    let p = near_primitives::bandwidth_scheduler::BandwidthSchedulerParams::new(
        std::num::NonZeroU64::new(1).unwrap(),
        &cfg,
    );
    assert_eq!(bw.max_shard_bandwidth, 4_500_000);
    assert_eq!(bw.max_single_grant, 4_194_304);
    assert_eq!(bw.max_allowance, 4_500_000);
    assert_eq!(bw.max_base_bandwidth, 100_000);
    assert_eq!(p.base_bandwidth, 100_000);
    assert_eq!(p.max_allowance, 4_500_000);
    assert_eq!(p.max_shard_bandwidth, 4_500_000);
    d["schema"] = json!("near-arena-runtime-config-v2");
    d["slice_parameters"]["bandwidth_scheduler"] = json!({
        "max_shard_bandwidth": bw.max_shard_bandwidth,
        "max_single_grant": bw.max_single_grant,
        "max_allowance": bw.max_allowance,
        "max_base_bandwidth": bw.max_base_bandwidth,
        "max_receipt_size": max_receipt_size,
        "num_shards": 1,
        "derived_base_bandwidth": p.base_bandwidth,
        "derived_fair_link_bandwidth": p.max_shard_bandwidth,
    });
    d
}

pub fn cmd_params(args: &[String]) -> i32 {
    let d = runtime_config_json();
    let digest = hash(crate::jcs(&d).as_bytes()).0;
    eprintln!("runtime_config_digest (v2) = sha256:{}", hex::encode(digest));
    let s = serde_json::to_string_pretty(&d).unwrap() + "\n";
    match arg(args, "--out") {
        Some(p) => std::fs::write(p, s).unwrap(),
        None => print!("{s}"),
    }
    0
}
