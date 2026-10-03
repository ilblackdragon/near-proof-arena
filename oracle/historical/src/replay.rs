//! Historical replay: run the slice on AUTHENTIC mainnet trie nodes.
//!
//! `build` takes a context file (block/chunk fields and the authentic receipts,
//! as RPC `ReceiptView` JSON) plus nearcore state-sync parts (raw `StatePart`
//! bytes obtained from mainnet peers) of the shard trie rooted at
//! `pre_state_root`. The union of the parts' trie nodes is used as a partial
//! trie (`Trie::from_recorded_storage`), exactly as a stateless validator uses
//! a chunk state witness. The real pinned `Runtime::apply` runs on it with a
//! recorder; whatever it read is saved as `apply_witness.bin` (borsh
//! `PartialState`), which is all `replay` needs to re-run the case.
//!
//! Every trie node is addressed by its SHA-256 hash, so a successful run proves
//! that the values read (receiver accounts, delayed-receipt indices,
//! bandwidth-scheduler state, ...) are the ones committed by `pre_state_root`.
//! The partial trie never contains a node that did not come from mainnet.
//!
//! The apply/observe logic mirrors `oracle/src/exec.rs` (the judge's frozen,
//! digest-pinned generator, which only builds full synthetic tries and is
//! deliberately left untouched); request/witness/claim encodings and the
//! independent domain check are `oracle/src/enc.rs` and `oracle/src/domain.rs`
//! compiled in unchanged.

use crate::{domain, enc};
use enc::{Claim, Request};
use near_parameters::RuntimeConfigStore;
use near_primitives::apply::ApplyChunkReason;
use near_primitives::bandwidth_scheduler::BlockBandwidthRequests;
use near_primitives::congestion_info::{BlockCongestionInfo, ExtendedCongestionInfo};
use near_primitives::hash::{CryptoHash, hash};
use near_primitives::merkle::merklize;
use near_primitives::receipt::Receipt;
use near_primitives::state::PartialState;
use near_primitives::state_part::StatePart;
use near_primitives::test_utils::MockEpochInfoProvider;
use near_primitives::transaction::{ExecutionOutcomeWithId, ExecutionStatus};
use near_primitives::types::{EpochId, EpochInfoProvider, Gas, ShardId};
use near_primitives::views::ReceiptView;
use near_store::trie::AccessOptions;
use near_store::{PartialStorage, Trie};
use node_runtime::{ApplyState, Runtime, SignedValidPeriodTransactions};
use serde_json::json;
use std::collections::BTreeMap;
use std::path::Path;
use std::str::FromStr;

pub const NEARCORE_COMMIT: &str = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993";
pub const APPLY_WITNESS: &str = "apply_witness.bin";

/// Columns nearcore may legitimately write when a real mainnet pre-state is
/// applied at a later block height than the one it was produced for:
/// PROMISE_YIELD_INDICES (0x0a) and PROMISE_YIELD_TIMEOUT (0x0b) -- removal of
/// yield timeouts that fall due (`Runtime::process_receipts` stage 4, after all
/// incoming receipts). They are outside the slice (the projection root only
/// covers Account writes); the run is still required to produce exactly one
/// outcome per batch receipt and no outgoing receipts other than the refunds.
pub const TOLERATED_COLS: &[u8] = &[0x0a, 0x0b];

fn hx(x: &CryptoHash) -> String {
    hex::encode(x.as_ref())
}

fn storage_from_values(mut vals: Vec<Vec<u8>>) -> PartialStorage {
    vals.sort();
    vals.dedup();
    PartialStorage { nodes: PartialState::TrieValues(vals.into_iter().map(Into::into).collect()) }
}

pub fn storage_from_parts(paths: &[String]) -> Result<PartialStorage, String> {
    let mut vals = vec![];
    for p in paths {
        let bytes = std::fs::read(p).map_err(|e| format!("{p}: {e}"))?;
        let part = StatePart::from_bytes(bytes).map_err(|e| format!("{p}: {e}"))?;
        let PartialState::TrieValues(v) = part.to_partial_state().map_err(|e| format!("{p}: {e}"))?;
        vals.extend(v.into_iter().map(|x| x.to_vec()));
    }
    Ok(storage_from_values(vals))
}

pub fn storage_from_apply_witness(path: &Path) -> Result<PartialStorage, String> {
    let b = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let ps: PartialState = borsh::from_slice(&b).map_err(|e| format!("apply_witness: {e}"))?;
    let PartialState::TrieValues(v) = ps;
    Ok(storage_from_values(v.into_iter().map(|x| x.to_vec()).collect()))
}

pub fn parse_ctx(v: &serde_json::Value) -> Result<Request, String> {
    let s = |k: &str| v.get(k).and_then(|x| x.as_str()).ok_or(format!("ctx.{k} missing"));
    let u = |k: &str| v.get(k).and_then(|x| x.as_u64()).ok_or(format!("ctx.{k} missing"));
    let receipts: Vec<Receipt> = v
        .get("receipts")
        .and_then(|x| x.as_array())
        .ok_or("ctx.receipts missing")?
        .iter()
        .map(|r| {
            let view: ReceiptView = serde_json::from_value(r.clone()).map_err(|e| format!("receipt view: {e}"))?;
            Receipt::try_from(view).map_err(|e| format!("receipt view -> receipt: {e}"))
        })
        .collect::<Result<_, _>>()?;
    Ok(Request {
        protocol_version: u("protocol_version")? as u32,
        chain_id: s("chain_id")?.to_string(),
        shard_id: u("shard_id")?,
        block_height: u("block_height")?,
        block_gas_price: s("block_gas_price")?.parse().map_err(|e| format!("block_gas_price: {e}"))?,
        gas_limit: u("gas_limit")?,
        pre_state_root: CryptoHash::from_str(s("pre_state_root")?).map_err(|e| format!("pre_state_root: {e}"))?,
        receipts,
    })
}

pub struct Executed {
    pub request: Request,
    pub claim: Option<Claim>,
    pub witness_values: Vec<Vec<u8>>,
    pub apply_witness: Option<PartialStorage>,
    pub nearcore: serde_json::Value,
    pub clean: bool,
    pub problems: Vec<String>,
    /// receiver Account values under pre_state_root (read through the partial trie)
    pub receiver_pre: BTreeMap<Vec<u8>, Vec<u8>>,
}

/// Execute `req` with the real `Runtime::apply` on the partial trie backed by
/// `storage`. Single-shard test layout for routing, as in the oracle;
/// `req.shard_id` is bound in request/claim but non-semantic for the slice.
pub fn run(req: Request, storage: &PartialStorage) -> Executed {
    let pre_root = req.pre_state_root;
    let mk = || Trie::from_recorded_storage(storage.clone(), pre_root, false);
    let mut problems = vec![];
    let mut receiver_pre = BTreeMap::new();
    for r in &req.receipts {
        let k = domain::account_key(r.receiver_id().as_str());
        match mk().get(&k, AccessOptions::DEFAULT) {
            Ok(Some(v)) => {
                receiver_pre.insert(k, v);
            }
            Ok(None) => {}
            Err(e) => problems.push(format!("receiver path not in the provided trie nodes: {e:?}")),
        }
    }
    let fail = |req: Request, nearcore, problems, receiver_pre| Executed {
        request: req,
        claim: None,
        witness_values: vec![],
        apply_witness: None,
        nearcore,
        clean: false,
        problems,
        receiver_pre,
    };
    if !problems.is_empty() {
        return fail(req, json!({"apply": "not run"}), problems, receiver_pre);
    }

    let config = RuntimeConfigStore::new(None).get_config(req.protocol_version).clone();
    let epoch_info_provider = MockEpochInfoProvider::default();
    let shard_layout = epoch_info_provider.shard_layout(&EpochId::default()).unwrap();
    let shard_uid = shard_layout.shard_uids().next().unwrap();
    let congestion_info = BlockCongestionInfo::new(
        shard_layout.shard_ids().map(|s| (s, ExtendedCongestionInfo::default())).collect(),
    );
    let apply_state = ApplyState {
        apply_reason: ApplyChunkReason::UpdateTrackedShard,
        block_height: req.block_height,
        prev_block_hash: CryptoHash::default(),
        shard_id: shard_uid.shard_id(),
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
        congestion_info,
        bandwidth_requests: BlockBandwidthRequests::empty(),
        on_post_state_ready: None,
    };

    // slice witness: nodes + values on the paths to every receiver's Account key
    let rec = mk().recording_reads_new_recorder();
    for r in &req.receipts {
        let _ = rec.get(&domain::account_key(r.receiver_id().as_str()), AccessOptions::DEFAULT).unwrap();
    }
    let proof = rec.recorded_storage().unwrap();
    let PartialState::TrieValues(values) = &proof.nodes;
    let witness_values: Vec<Vec<u8>> = values.iter().map(|v| v.to_vec()).collect();

    let trie = mk().recording_reads_new_recorder();
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
        Err(_) => return fail(req, json!({"apply": "panicked"}), vec!["Runtime::apply panicked".into()], receiver_pre),
        Ok(Err(e)) => {
            return fail(
                req,
                json!({"apply": "error", "error": format!("{e:?}")}),
                vec![format!("Runtime::apply error: {e:?}")],
                receiver_pre,
            );
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
                problems.push(format!("receipt {} status {:?}", hx(&o.id), s));
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
        problems.push(format!("outgoing receipts ({}) != outcome receipt_ids ({})", out_ids.len(), refund_ids.len()));
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
    let account_changes: Vec<_> = all.iter().filter(|(k, _)| k[0] == 0).cloned().collect();
    let other: Vec<String> = all.iter().filter(|(k, _)| k[0] != 0).map(|(k, _)| hex::encode(k)).collect();
    let tolerated: Vec<String> = all
        .iter()
        .filter(|(k, _)| TOLERATED_COLS.contains(&k[0]))
        .map(|(k, _)| hex::encode(k))
        .collect();
    if other.iter().any(|k| k != "0f" && !tolerated.contains(k)) {
        problems.push(format!("non-Account keys other than bandwidth scheduler / yield queue changed: {other:?}"));
    }
    for (k, v) in &account_changes {
        match v {
            None => problems.push("account deleted".into()),
            Some(v) if v.len() != 72 => problems.push("account value length changed".into()),
            _ => {}
        }
        if !receiver_pre.contains_key(k) {
            problems.push("account key inserted or not a receiver".into());
        }
    }
    let base = mk();
    let slice_root = base.update(account_changes.clone(), AccessOptions::DEFAULT).unwrap().new_root;
    let full_again = base.update(all.clone(), AccessOptions::DEFAULT).unwrap().new_root;
    let decomposition_ok = full_again == result.state_root;
    if !decomposition_ok {
        problems.push("decomposition failed: pre ⊕ changes != Runtime::apply root".into());
    }
    if !account_changes.is_empty() {
        let wt = Trie::from_recorded_storage(proof.clone(), pre_root, false);
        let r3 = wt.update(account_changes.clone(), AccessOptions::DEFAULT).unwrap().new_root;
        if r3 != slice_root {
            problems.push("witness-only slice root mismatch".into());
        }
    }
    let apply_witness = result.proof.clone();
    let full_recorded = result.proof.as_ref().map(|p| {
        let PartialState::TrieValues(v) = &p.nodes;
        v.iter().map(|x| x.len()).sum::<usize>()
    });
    let claim = Claim {
        protocol_version: req.protocol_version,
        chain_id: req.chain_id.clone(),
        shard_id: req.shard_id,
        block_height: req.block_height,
        block_gas_price: req.block_gas_price,
        gas_limit: req.gas_limit,
        pre_state_root: pre_root.0,
        receipt_count: n as u32,
        receipts_commitment: hash(&borsh::to_vec(&(ShardId::new(req.shard_id), &req.receipts)).unwrap()).0,
        slice_post_root: slice_root.0,
        outcome_root: outcome_root.0,
        refund_count: result.outgoing_receipts.len() as u32,
        refund_receipts_commitment: hash(&borsh::to_vec(&result.outgoing_receipts).unwrap()).0,
        gas_burnt_total: gas_total,
        tokens_burnt_total: tokens_total,
    };
    let nearcore = json!({
        "apply": "ok",
        "apply_ns": apply_ns,
        "full_apply_state_root": hx(&result.state_root),
        "slice_post_root": hx(&slice_root),
        "decomposition_ok": decomposition_ok,
        "non_account_keys_changed": other,
        "non_slice_writes_tolerated": tolerated,
        "outcome_statuses": statuses,
        "outgoing_receipts": result.outgoing_receipts.len(),
        "outgoing_receipt_ids": out_ids.iter().map(|h| h.to_string()).collect::<Vec<_>>(),
        "delayed_receipts_count": result.delayed_receipts_count,
        "tx_burnt_amount": result.stats.balance.tx_burnt_amount.as_yoctonear().to_string(),
        "full_apply_recorded_bytes": full_recorded,
        "slice_witness_values": witness_values.len(),
        "slice_witness_bytes": witness_values.iter().map(|v| v.len()).sum::<usize>(),
    });
    let clean = problems.is_empty();
    Executed { request: req, claim: Some(claim), witness_values, apply_witness, nearcore, clean, problems, receiver_pre }
}

/// Build a historical case directory.
pub fn build(req: Request, storage: &PartialStorage, out: &Path) -> Result<serde_json::Value, String> {
    let ex = run(req, storage);
    let aw = ex.apply_witness.as_ref().ok_or_else(|| format!("apply failed: {:?}", ex.problems))?;
    std::fs::create_dir_all(out).map_err(|e| e.to_string())?;
    let req_bytes = ex.request.encode();
    let witness = enc::encode_witness(&ex.request.pre_state_root, &ex.witness_values);
    let wbytes: usize = ex.witness_values.iter().map(|v| v.len()).sum();
    let dom = domain::check(&ex.request, &ex.receiver_pre, wbytes);
    let aw_bytes = borsh::to_vec(&aw.nodes).unwrap();
    std::fs::write(out.join("request.bin"), &req_bytes).unwrap();
    std::fs::write(out.join("witness.bin"), &witness).unwrap();
    std::fs::write(out.join(APPLY_WITNESS), &aw_bytes).unwrap();
    // the independent Rust domain simulation must agree with nearcore (as in the oracle)
    let mut consistent = true;
    if let (Ok(sim), Some(c)) = (&dom, &ex.claim) {
        consistent = sim.tokens_burnt_total == c.tokens_burnt_total && sim.refunds as u32 == c.refund_count;
    }
    let in_domain = dom.is_ok() && ex.clean && consistent;
    let claim_bytes = ex.claim.as_ref().filter(|_| in_domain).map(|c| c.encode());
    if let (Some(c), Some(cb)) = (&ex.claim, &claim_bytes) {
        std::fs::write(out.join("expected_claim.bin"), cb).unwrap();
        assert_eq!(Claim::decode(cb).unwrap(), *c);
        assert!(enc::decode_request(&req_bytes).is_ok());
    }
    let diag = json!({
        "schema": "near-arena-oracle-case-v1",
        "case_class": "historical",
        "nearcore_commit": NEARCORE_COMMIT,
        "synthetic_state": false,
        "in_domain": in_domain,
        "domain_sim_consistent_with_nearcore": consistent,
        "domain_reason": dom.as_ref().err(),
        "nearcore": ex.nearcore,
        "nearcore_problems": ex.problems,
        "claim": ex.claim.as_ref().filter(|_| in_domain).map(|c| c.to_json()),
        "receiver_pre_values": ex.receiver_pre.iter().map(|(k, v)| json!({"key": hex::encode(k), "value": hex::encode(v)})).collect::<Vec<_>>(),
        "sizes": {
            "request_bytes": req_bytes.len(),
            "witness_bytes": witness.len(),
            "apply_witness_bytes": aw_bytes.len(),
            "receipts": ex.request.receipts.len(),
        },
        "digests": {
            "request.bin": format!("sha256:{}", hex::encode(hash(&req_bytes).0)),
            "witness.bin": format!("sha256:{}", hex::encode(hash(&witness).0)),
            "apply_witness.bin": format!("sha256:{}", hex::encode(hash(&aw_bytes).0)),
            "expected_claim.bin": claim_bytes.as_ref().map(|c| format!("sha256:{}", hex::encode(hash(c).0))),
        }
    });
    std::fs::write(out.join("diagnostics.json"), serde_json::to_string_pretty(&diag).unwrap() + "\n").unwrap();
    if !in_domain {
        return Err(format!("not in domain / not clean: {:?} {:?}", dom.err(), ex.problems));
    }
    Ok(diag)
}

/// Re-run a historical case from request.bin + apply_witness.bin only and check
/// that witness.bin and expected_claim.bin are reproduced byte for byte.
pub fn replay(dir: &Path) -> Result<(), String> {
    let req = enc::decode_request(&std::fs::read(dir.join("request.bin")).map_err(|e| e.to_string())?)?;
    let storage = storage_from_apply_witness(&dir.join(APPLY_WITNESS))?;
    let ex = run(req, &storage);
    if !ex.clean {
        return Err(format!("not clean: {:?}", ex.problems));
    }
    let w = enc::encode_witness(&ex.request.pre_state_root, &ex.witness_values);
    if w != std::fs::read(dir.join("witness.bin")).map_err(|e| e.to_string())? {
        return Err("witness.bin differs".into());
    }
    let wb: usize = ex.witness_values.iter().map(|v| v.len()).sum();
    domain::check(&ex.request, &ex.receiver_pre, wb)?;
    if ex.claim.map(|c| c.encode()) != std::fs::read(dir.join("expected_claim.bin")).ok() {
        return Err("expected_claim.bin differs".into());
    }
    Ok(())
}
