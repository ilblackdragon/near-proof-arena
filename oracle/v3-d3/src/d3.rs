//! Domain-D3α classification, metadata, code-blob mutants and case writing of one honest
//! witness (README.md). `InD3α` (docs/requirements/D3_WASM_REQUIREMENTS.md §1.1,
//! spec/lean/v3/NearSpecV3/Wasm/DomainD3.lean) =
//!   InD2 with `e.wasm` lifted (src/../v3-d1/src/d2.rs `analyze`, unchanged)
//!   ∧ `c.no_resharding`  one epoch, no epoch start in the segment, no split gate (`noResharding`)
//!   ∧ `e.float`          no executed contract has a float value type or opcode
//!   ∧ `e.curve_host`     no executed contract imports a `curveHosts` function (ed25519_verify is
//!                        modelled by the Lean spec and only recorded, `features.ed25519_import`)
//!   ∧ `o.unknown_receipt` / `o.code_unknown`  (oracle limits: an executed receipt the oracle
//!                        cannot find, a code hash outside the registry; never seen so far).
//! The per-chunk WASM gas cap `G_α` is not set yet; `features.fc_gas_burnt` records the gas.
//! "Executed contract" = the code a FunctionCall that reaches its dispatch point runs: the
//! receiver's code at that moment (the pre-state's, or one deployed earlier in the chunk —
//! tracked through the receipts in execution order with nearcore's per-receipt rollback).

use crate::chaingen::{GenOpts, Stats};
use crate::claim::{Built, block_rec};
use crate::d2::Analysis;
use crate::d3judge::ColdJudge;
use crate::enc::{Claim, encode_witness};
use crate::mutate::{Judge, Mutant, drop_each_node, mutants};
use near_chain::ChainStoreAccess;
use near_chain::stateless_validation::chunk_validation::MainTransition;
use near_client::Client;
use near_primitives::account::AccountContract;
use near_primitives::action::Action;
use near_primitives::errors::{ActionErrorKind, TxExecutionError};
use near_primitives::hash::CryptoHash;
use near_primitives::receipt::{Receipt, ReceiptSource, VersionedReceiptEnum};
use near_primitives::sharding::{ShardChunkHeader, ShardChunkHeaderInner};
use near_primitives::state::PartialState;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::transaction::{ExecutionStatus, SignedTransaction};
use near_primitives::types::AccountId;
use near_store::Trie;
use rand::Rng;
use rand::rngs::StdRng;
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::Path;

/// D3-specific counters (summary.json `d3`).
#[derive(Default)]
pub struct D3Stats {
    pub counters: BTreeMap<String, u64>,
}
impl D3Stats {
    pub fn add(&mut self, k: &str, n: u64) {
        *self.counters.entry(k.to_string()).or_default() += n;
    }
}

#[derive(Clone, Debug)]
pub struct Executed {
    pub hash: CryptoHash,
    pub account: AccountId,
    /// "state" (pre-state code) or "deployed_in_chunk"
    pub source: &'static str,
}

pub struct D3Analysis {
    pub violations: Vec<&'static str>,
    pub executed: Vec<Executed>,
    pub features: BTreeMap<String, serde_json::Value>,
    pub chain_id_import: bool,
}

fn status_kind(s: &ExecutionStatus) -> Option<String> {
    match s {
        ExecutionStatus::Failure(TxExecutionError::ActionError(e)) => {
            let k = format!("{:?}", e.kind);
            if let ActionErrorKind::FunctionCallError(fe) = &e.kind {
                let f = format!("{fe:?}");
                let head: String = f.chars().take_while(|c| c.is_ascii_alphanumeric()).collect();
                let inner: String = f[head.len()..].trim_start_matches('(').chars().take_while(|c| c.is_ascii_alphanumeric()).collect();
                // HostError / ExecutionError text → variant (as oracle/d3-ttn err_kind)
                if f.contains("Exceeded the prepaid gas") {
                    return Some("FunctionCallError:GasExceeded".into());
                }
                if head == "ExecutionError" {
                    // a host error / trap stored as its Display text: keep the text's head
                    let t = f.split('"').nth(1).unwrap_or("");
                    let t: String = t.split(|c: char| c == ':' || c == ',' || c == '(').next().unwrap_or("").chars().take(48).collect();
                    return Some(format!("FunctionCallError:ExecutionError:{}", t.trim().replace(' ', "_")));
                }
                return Some(format!("FunctionCallError:{head}:{inner}"));
            }
            Some(k.split(|c: char| c == ' ' || c == '{' || c == '(').next().unwrap_or("").to_string())
        }
        _ => None,
    }
}

fn find_yield_receipt(pre: &Trie, account: &AccountId, id: &CryptoHash) -> Result<Option<Receipt>, String> {
    let mut prefix = vec![12u8]; // PROMISE_YIELD_RECEIPT
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

/// Walk the main transition's executed receipts in execution order (the stored outcome order)
/// and determine the contracts executed (see the module doc).
pub fn analyze_d3(client: &Client, built: &Built, w: &ChunkStateWitness, accesses: &[CryptoHash]) -> Result<D3Analysis, String> {
    let mut v: Vec<&'static str> = Vec::new();
    let add = |v: &mut Vec<&'static str>, s: &'static str| {
        if !v.contains(&s) {
            v.push(s)
        }
    };
    let c = &built.claim;
    let mut an = D3Analysis { violations: vec![], executed: vec![], features: BTreeMap::new(), chain_id_import: false };
    if !(c.epochs.len() == 1 && c.epoch_start_after.iter().all(|x| *x == 0) && c.apply_facts.iter().all(|f| f.split_gate.is_none())) {
        add(&mut v, "c.no_resharding");
    }
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
    let pv = crate::judge::pre_validate(client, w)?;
    let incoming: Vec<Receipt> = match pv.main_transition_params {
        MainTransition::NewChunk { new_chunk_data, .. } => new_chunk_data.receipts,
        MainTransition::Genesis { .. } => vec![],
    };
    let store = client.chain.chain_store();
    let mut by_id: HashMap<CryptoHash, Receipt> = incoming.iter().map(|r| (*r.receipt_id(), r.clone())).collect();
    let processed = store.get_processed_receipt_ids(b2.hash(), sid).map(|x| (*x).clone()).unwrap_or_default();
    for m in &processed {
        if matches!(m.source(), ReceiptSource::ReceiptToTxGc) {
            continue;
        }
        if let Some(r) = store.get_receipt(m.receipt_id()) {
            by_id.insert(*m.receipt_id(), (*r).clone());
        }
    }
    let tx_hashes: HashSet<CryptoHash> = w.transactions().iter().map(|t| t.get_hash()).collect();
    let outcome_ids =
        near_store::adapter::StoreAdapter::chain_store(&client.chain.chain_store().store()).get_outcomes_by_block_hash_and_shard_id(b2.hash(), sid);
    // committed code per account (None = no code / deleted), on top of the pre-state
    let mut code: HashMap<AccountId, Option<CryptoHash>> = HashMap::new();
    let pre_code = |a: &AccountId| -> Result<(Option<CryptoHash>, bool), String> {
        Ok(match near_store::get_account(&pre, a).map_err(|e| e.to_string())? {
            None => (None, false),
            Some(acc) => match acc.contract().as_ref() {
                AccountContract::None => (None, false),
                AccountContract::Local(h) => (Some(*h), false),
                _ => (None, true),
            },
        })
    };
    let (mut n_fc, mut n_fc_code, mut n_fc_fail, mut n_logs, mut n_new_receipts, mut n_callbacks, mut gas_fc) = (0u64, 0u64, 0u64, 0u64, 0u64, 0u64, 0u64);
    let mut fail_kinds: BTreeMap<String, u64> = BTreeMap::new();
    let mut executed: Vec<Executed> = Vec::new();
    let mut deployed_hashes: HashSet<CryptoHash> = HashSet::new();
    for id in &outcome_ids {
        if tx_hashes.contains(id) {
            continue;
        }
        let outs = store.get_outcomes_by_id(id).map_err(|e| format!("{e:?}"))?;
        let Some(o) = outs.into_iter().find(|o| &o.block_hash == b2.hash()) else { continue };
        let outcome = o.outcome_with_id.outcome;
        let executor = outcome.executor_id.clone();
        let r = match by_id.get(id) {
            Some(x) => x.clone(),
            None => match near_store::get_postponed_receipt(&pre, &executor, *id).map_err(|e| e.to_string())? {
                Some(r) => r,
                None => match find_yield_receipt(&pre, &executor, id)? {
                    Some(r) => r,
                    None => {
                        add(&mut v, "o.unknown_receipt");
                        continue;
                    }
                },
            },
        };
        let (actions, has_inputs) = match r.versioned_receipt() {
            VersionedReceiptEnum::Action(a) | VersionedReceiptEnum::PromiseYield(a) => (a.actions().to_vec(), !a.input_data_ids().is_empty()),
            _ => (vec![], false),
        };
        let reached = |j: usize| -> bool {
            match &outcome.status {
                ExecutionStatus::Failure(TxExecutionError::ActionError(e)) => match e.index {
                    None => true,
                    Some(i) => (j as u64) < i || ((j as u64) == i && !matches!(e.kind, ActionErrorKind::AccountDoesNotExist { .. })),
                },
                _ => true,
            }
        };
        let a = r.receiver_id().clone();
        let mut tentative: Option<Option<CryptoHash>> = None; // this receipt's code change of `a`
        let mut fc_here = false;
        for (j, act) in actions.iter().enumerate() {
            if !reached(j) {
                break;
            }
            match act {
                Action::CreateAccount(_) => tentative = Some(None),
                Action::DeleteAccount(_) => tentative = Some(None),
                Action::DeployContract(d) => {
                    let h = CryptoHash::hash_bytes(&d.code);
                    deployed_hashes.insert(h);
                    tentative = Some(Some(h));
                }
                Action::UseGlobalContract(_) => add(&mut v, "w.shape"),
                Action::FunctionCall(_) => {
                    n_fc += 1;
                    fc_here = true;
                    let cur = match tentative {
                        Some(t) => t,
                        None => match code.get(&a) {
                            Some(t) => *t,
                            None => {
                                let (h, global) = pre_code(&a)?;
                                if global {
                                    add(&mut v, "w.shape");
                                }
                                h
                            }
                        },
                    };
                    if let Some(h) = cur {
                        n_fc_code += 1;
                        // nearcore records a contract access iff the pre-state trie holds this
                        // code hash for the account (function_call.rs record_contract_call)
                        let source = if pre_code(&a)?.0 == Some(h) { "state" } else { "deployed_in_chunk" };
                        if !executed.iter().any(|e| e.hash == h && e.account == a && e.source == source) {
                            executed.push(Executed { hash: h, account: a.clone(), source });
                        }
                    }
                }
                _ => {}
            }
        }
        if matches!(outcome.status, ExecutionStatus::SuccessValue(_) | ExecutionStatus::SuccessReceiptId(_)) {
            if let Some(t) = tentative {
                code.insert(a.clone(), t);
            }
        }
        if fc_here {
            gas_fc += outcome.gas_burnt.as_gas();
            n_logs += outcome.logs.len() as u64;
            n_new_receipts += outcome.receipt_ids.len() as u64;
            if has_inputs {
                n_callbacks += 1;
            }
            if let Some(k) = status_kind(&outcome.status) {
                n_fc_fail += 1;
                *fail_kinds.entry(k).or_default() += 1;
            }
        }
    }
    // contract facts
    let reg = crate::d3contracts::registry();
    let mut names = BTreeSet::new();
    let mut ed = false;
    for e in &executed {
        match reg.by_hash.get(&e.hash) {
            None => add(&mut v, "o.code_unknown"),
            Some((n, code)) => {
                names.insert(n.to_string());
                let f = crate::d3contracts::code_facts(code);
                if f.float {
                    add(&mut v, "e.float");
                }
                if !f.curve_imports.is_empty() {
                    add(&mut v, "e.curve_host");
                }
                ed |= f.ed25519_import;
                an.chain_id_import |= f.chain_id_import;
            }
        }
    }
    // nearcore's contract accesses = the executed codes read from the pre-state
    let from_state: BTreeSet<CryptoHash> = executed.iter().filter(|e| e.source == "state").map(|e| e.hash).collect();
    let acc: BTreeSet<CryptoHash> = accesses.iter().copied().collect();
    an.features.insert("accesses_equal_state_executed".into(), json!(from_state == acc));
    an.features.insert("n_function_calls".into(), json!(n_fc));
    an.features.insert("n_function_calls_with_code".into(), json!(n_fc_code));
    an.features.insert("n_fc_failures".into(), json!(n_fc_fail));
    an.features.insert("fc_failure_kinds".into(), json!(fail_kinds));
    an.features.insert("n_logs".into(), json!(n_logs));
    an.features.insert("n_promises".into(), json!(n_new_receipts));
    an.features.insert("n_callbacks".into(), json!(n_callbacks));
    an.features.insert("fc_gas_burnt".into(), json!(gas_fc));
    an.features.insert("contracts_ran".into(), json!(names));
    an.features.insert("deployed_in_chunk".into(), json!(deployed_hashes.len()));
    an.features.insert("ran_deployed_in_chunk".into(), json!(executed.iter().filter(|e| e.source == "deployed_in_chunk").count()));
    an.features.insert("ed25519_import".into(), json!(ed));
    an.executed = executed;
    an.violations = v;
    Ok(an)
}

// ---------------------------------------------------------------------------------------------
// mutants (D2's header and trusted-fact mutants, oracle/v3-d1/src/d2.rs, private there)
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
    }
    {
        let near_primitives::congestion_info::CongestionInfo::V1(c1) = x.congestion_info;
        if c1.buffered_receipts_gas != 0 || c1.delayed_receipts_gas != 0 || c1.receipt_bytes != 0 {
            let mut y = x.clone();
            let near_primitives::congestion_info::CongestionInfo::V1(ref mut c) = y.congestion_info;
            c.buffered_receipts_gas ^= 1;
            push("hdr2.congestion.buffered_gas", y);
        }
    }
    {
        let near_primitives::bandwidth_scheduler::BandwidthRequests::V1(br) = &x.bandwidth_requests;
        if !br.requests.is_empty() {
            let mut y = x.clone();
            let near_primitives::bandwidth_scheduler::BandwidthRequests::V1(ref mut b) = y.bandwidth_requests;
            b.requests.pop();
            push("hdr2.bandwidth_requests.drop", y);
        }
    }
    out
}

/// D2's derived trusted-fact mutants (see oracle/v3-d1/src/d2.rs `fact_mutants`).
fn fact_mutants(built: &Built, an: &Analysis) -> Vec<(Mutant, &'static str)> {
    let mut out = Vec::new();
    let c = &built.claim;
    if let Some(s) = an.stakes.iter().filter(|x| x.1).map(|x| x.0).min() {
        let mut c2 = c.clone();
        c2.apply_facts[0].minimum_stake = s + 1;
        out.push((Mutant { name: "t.minimum_stake.raise(derived)".into(), claim: c2, witness: vec![], judge: Judge::Nearcore }, "reject"));
    }
    if let Some(s) = an.stakes.iter().filter(|x| x.2).map(|x| x.0).max() {
        let mut c2 = c.clone();
        c2.apply_facts[0].minimum_stake = s;
        out.push((Mutant { name: "t.minimum_stake.lower(derived)".into(), claim: c2, witness: vec![], judge: Judge::Nearcore }, "reject"));
    }
    if an.eth_created {
        let mut c2 = c.clone();
        c2.chain_id = "mainnet".into();
        out.push((Mutant { name: "t.chain_id.mainnet(derived)".into(), claim: c2, witness: vec![], judge: Judge::Nearcore }, "reject"));
    }
    out
}

/// Code-blob mutants: (name, codes).
fn code_mutants(codes: &[Vec<u8>], rng: &mut StdRng) -> Vec<(String, Vec<Vec<u8>>)> {
    let mut out = Vec::new();
    let reg = crate::d3contracts::registry();
    for i in 0..codes.len().min(3) {
        let mut c = codes.to_vec();
        c.remove(i);
        out.push((format!("code.drop.{i}"), c));
        let mut c = codes.to_vec();
        let j = rng.gen_range(0..c[i].len());
        c[i][j] ^= 1 << rng.gen_range(0..8);
        out.push((format!("code.flip.{i}"), c));
    }
    if codes.len() > 1 {
        out.push(("code.none".into(), vec![]));
        let mut c = codes.to_vec();
        c.reverse();
        out.push(("code.reorder".into(), c));
    }
    if !codes.is_empty() {
        let mut c = codes.to_vec();
        c.push(codes[0].clone());
        out.push(("code.duplicate".into(), c));
        // a truncated blob in place of the needed one
        let mut c = codes.to_vec();
        let l = c[0].len();
        c[0].truncate(l / 2);
        out.push(("code.truncate.0".into(), c));
    }
    // an unneeded registry code / random bytes appended
    let unneeded: Vec<&Vec<u8>> = reg.by_hash.values().map(|x| &x.1).filter(|x| !codes.contains(x)).collect();
    if !unneeded.is_empty() {
        let mut c = codes.to_vec();
        c.push(unneeded[rng.gen_range(0..unneeded.len())].clone());
        out.push(("code.extra_unneeded".into(), c));
    }
    let mut c = codes.to_vec();
    c.push((0..rng.gen_range(1..200)).map(|_| rng.r#gen()).collect());
    out.push(("code.extra_garbage".into(), c));
    out
}

pub struct D3Ctx<'a> {
    pub tracker: &'a Client,
    pub client: &'a Client,
    pub ci: usize,
    pub judge: &'a ColdJudge,
    pub built: &'a Built,
    pub sw: &'a ChunkStateWitness,
    pub wb: &'a [u8],
    pub accesses: &'a [CryptoHash],
    pub codes: &'a [Vec<u8>],
    pub verdict: &'a Result<(), String>,
    pub warm: &'a Result<(), String>,
    pub cold_no_codes: Option<&'a Result<(), String>>,
    pub labels: &'a HashMap<CryptoHash, String>,
    pub chain_idx: usize,
    pub params: &'a str,
    pub n_shards: usize,
    pub out: &'a Path,
    pub o: &'a GenOpts,
    pub rng: &'a mut StdRng,
    pub ood_count: &'a mut BTreeMap<String, usize>,
    pub d3_seen: &'a mut usize,
    pub drop_cap: usize,
    pub code_mutant_p: f64,
}

fn write_case(dir: &Path, claim: &Claim, witness: &[u8], codes: &[Vec<u8>], meta: serde_json::Value) {
    std::fs::create_dir_all(dir).unwrap();
    std::fs::write(dir.join("claim.bin"), claim.encode()).unwrap();
    std::fs::write(dir.join("witness.bin"), encode_witness(witness, codes)).unwrap();
    std::fs::write(dir.join("meta.json"), serde_json::to_string_pretty(&meta).unwrap()).unwrap();
}

fn vstr(r: &Result<(), String>) -> String {
    r.as_ref().map(|_| "ok".to_string()).unwrap_or_else(|e| e.clone())
}

/// Classification, metadata, mutants and writing of one honest witness.
pub fn write_d3_case(x: D3Ctx, stats: &mut Stats, d3s: &mut D3Stats) {
    let D3Ctx {
        tracker, client, ci, judge, built, sw, wb, accesses, codes, verdict, warm, cold_no_codes, labels, chain_idx, params,
        n_shards, out, o, rng, ood_count, d3_seen, drop_cap, code_mutant_p,
    } = x;
    let viol = match crate::d0::classify(tracker, built, sw, wb.len(), codes.len()) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("classify failed: {e}");
            return;
        }
    };
    let in_d0 = viol.is_empty();
    let viol1 = match crate::d1::classify(tracker, built, sw, &viol) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("d1 classify failed: {e}");
            return;
        }
    };
    let in_d1 = viol1.is_empty();
    let PartialState::TrieValues(vals) = &sw.main_state_transition().base_state;
    let base_bytes: usize = vals.iter().map(|x| x.len()).sum();
    // D2's analysis (w.no_code is a D0 condition D2 keeps; D2 reads code-free witnesses)
    let viol_nc: Vec<&'static str> = viol.iter().copied().filter(|x| *x != "w.no_code").collect();
    let an2 = match crate::d2::analyze(tracker, built, sw, &viol_nc, base_bytes) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("d2 analyze failed: {e}");
            return;
        }
    };
    let mut viol2 = an2.violations.clone();
    if !codes.is_empty() && !viol2.contains(&"w.no_code") {
        viol2.push("w.no_code");
    }
    let in_d2 = viol2.is_empty();
    let an3 = match analyze_d3(tracker, built, sw, accesses) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("d3 analyze failed: {e}");
            return;
        }
    };
    let mut viol3: Vec<&'static str> = an2.violations.iter().copied().filter(|x| *x != "e.wasm").collect();
    for x in &an3.violations {
        if !viol3.contains(x) {
            viol3.push(x);
        }
    }
    let in_d3 = viol3.is_empty();
    // the D2 classifier's e.wasm and the D3 walk agree on whether any contract ran
    let ran = !an3.executed.is_empty();
    if ran && !an2.violations.contains(&"e.wasm") {
        d3s.add("check.ran_but_no_e_wasm", 1);
    }
    let tx_results = crate::d2::tx_results(tracker, built, sw);
    let lab = |t: &SignedTransaction| labels.get(&t.get_hash()).cloned().unwrap_or_else(|| "unknown".into());
    let tx_labels: Vec<String> = sw.transactions().iter().map(lab).collect();
    let new_tx_labels: Vec<String> = sw.new_transactions().iter().map(lab).collect();
    let key = sw.chunk_production_key();
    let name = format!("{chain_idx:02}-h{}-s{}", key.height_created, key.shard_id);
    for v in &viol3 {
        *stats.by_violation.entry(v.to_string()).or_default() += 1;
    }
    let reg = crate::d3contracts::registry();
    let cname = |h: &CryptoHash| reg.by_hash.get(h).map(|x| x.0).unwrap_or("unknown");
    let code_meta: Vec<serde_json::Value> = codes
        .iter()
        .map(|c| {
            let h = CryptoHash::hash_bytes(c);
            json!({"hash": h.to_string(), "name": cname(&h), "len": c.len()})
        })
        .collect();
    let executed_meta: Vec<serde_json::Value> = an3
        .executed
        .iter()
        .map(|e| {
            let f = reg.by_hash.get(&e.hash).map(|x| crate::d3contracts::code_facts(&x.1)).unwrap_or_default();
            json!({"hash": e.hash.to_string(), "name": cname(&e.hash), "account": e.account.to_string(), "source": e.source,
                   "float": f.float, "curve_imports": f.curve_imports, "ed25519_import": f.ed25519_import})
        })
        .collect();
    let mut features = json!({
        "n_shards": n_shards,
        "rs": [built.claim.rs_data_parts, built.claim.rs_total_parts],
        "n_blocks": built.claim.blocks.len(),
        "n_implicit": built.implicit.len(),
        "n_receipts": match sw { ChunkStateWitness::V2(x) => x.source_receipt_proofs.values().map(|p| p.0.len()).sum::<usize>() },
        "witness_bytes": wb.len(),
        "base_state_bytes": base_bytes,
        "code_blobs": codes.len(),
        "code_bytes": codes.iter().map(|c| c.len()).sum::<usize>(),
    });
    for (k, v) in an2.features.iter().chain(an3.features.iter()) {
        features[k] = v.clone();
    }
    let meta = json!({
        "case": name, "kind": "honest", "chain_params": params,
        "nearcore": vstr(verdict),
        "nearcore_judge": "cold validator (empty compiled-contract cache) with the appended code blobs",
        "nearcore_warm_no_codes": vstr(warm),
        "nearcore_cold_no_codes": cold_no_codes.map(vstr),
        "expected_rel": verdict.is_ok(),
        "in_d0": in_d0, "d0_violations": viol, "expected_rel_d0": verdict.is_ok() && in_d0,
        "in_d1": in_d1, "d1_violations": viol1, "expected_rel_d1": verdict.is_ok() && in_d1,
        "in_d2": in_d2, "d2_violations": viol2, "expected_rel_d2": verdict.is_ok() && in_d2,
        "in_d3": in_d3, "d3_violations": viol3, "expected_rel_d3": verdict.is_ok() && in_d3,
        "contract_accesses": accesses.iter().map(|h| h.to_string()).collect::<Vec<_>>(),
        "codes": code_meta,
        "executed_contracts": executed_meta,
        "tx_labels": tx_labels, "tx_results": tx_results, "new_tx_labels": new_tx_labels,
        "action_results": an2.action_results, "receipt_classes": an2.receipt_classes,
        "features": features,
    });
    // coverage counters
    d3s.add("honest_with_function_calls", (an3.features.get("n_function_calls").cloned().unwrap_or_default().as_u64().unwrap_or(0) > 0) as u64);
    d3s.add("honest_with_executed_code", ran as u64);
    for k in ["n_function_calls", "n_function_calls_with_code", "n_fc_failures", "n_logs", "n_promises", "n_callbacks", "ran_deployed_in_chunk"] {
        d3s.add(&format!("sum.{k}"), an3.features.get(k).cloned().unwrap_or_default().as_u64().unwrap_or(0));
    }
    if let Some(m) = an3.features.get("fc_failure_kinds").cloned().unwrap_or_default().as_object() {
        for (k, n) in m {
            d3s.add(&format!("fail.{k}"), n.as_u64().unwrap_or(0));
        }
    }
    for e in &an3.executed {
        d3s.add(&format!("ran.{}.{}", cname(&e.hash), e.source), 1);
    }
    if an3.features.get("accesses_equal_state_executed").cloned().unwrap_or_default() == json!(false) {
        d3s.add("check.accesses_differ_from_state_executed", 1);
    }
    if in_d3 {
        d3s.add("d3.with_codes", (!codes.is_empty()) as u64);
        d3s.add("d3.multi_shard_receipts", (an2.receipt_classes.contains_key("incoming_action")) as u64);
    }
    if !in_d3 {
        let fam = viol3.join("+");
        let c = ood_count.entry(fam).or_default();
        if *c < o.ood_cap {
            *c += 1;
            stats.ood_written += 1;
            write_case(&out.join("ood").join(&name), &built.claim, wb, codes, meta);
        }
        return;
    }
    if in_d0 {
        stats.d0 += 1;
    }
    if in_d1 {
        stats.d1 += 1;
    }
    stats.positives += 1; // D3 cases
    write_case(&out.join("d3").join(&name), &built.claim, wb, codes, meta);
    *d3_seen += 1;
    let me = o.mutate_every;
    // the full mutant set for every me-th D3 case; code mutants only for a fraction
    // (`code_mutant_p`) of the other cases that executed state codes
    let full = me > 0 && *d3_seen % me == 0;
    let code_only = !full && !codes.is_empty() && rng.gen_bool(code_mutant_p);
    if !(verdict.is_ok() && (full || code_only)) {
        return;
    }
    let rs = |c: &Claim| (c.rs_data_parts, c.rs_total_parts);
    // (mutant, flags, derived verdict, codes)
    let mut ms: Vec<(Mutant, Option<Vec<u8>>, Option<&'static str>, Vec<Vec<u8>>)> = Vec::new();
    if full {
        let last = built.blocks.last().unwrap();
        let parent = if last.header().is_genesis() { None } else { client.chain.get_block(last.header().prev_hash()).ok().and_then(|b| block_rec(&b).ok()) };
        let m_cur = built.claim.apply_facts.first().map(|f| f.minimum_stake).unwrap_or(0);
        for m in mutants(&built.claim, sw, parent, rng) {
            if m.name.starts_with("t.minimum_stake") {
                let m2 = m.claim.apply_facts[0].minimum_stake;
                let (lo, hi) = (m_cur.min(m2), m_cur.max(m2));
                if an2.stakes.iter().any(|s| s.0 >= lo && s.0 < hi) {
                    continue;
                }
            }
            if m.name.starts_with("t.chain_id") {
                // the chain id is read by the ETH-implicit wallet hash (D2) and by contracts
                // importing `chain_id` (D3): such mutants are not judgeable by nearcore
                if an2.eth_created || an3.chain_id_import {
                    d3s.add("mutants_skipped.t.chain_id", 1);
                    continue;
                }
            }
            ms.push((m, None, None, codes.to_vec()));
        }
        if *d3_seen % (me * 2) == 0 {
            ms.extend(drop_each_node(&built.claim, sw, drop_cap).into_iter().map(|m| (m, None, None, codes.to_vec())));
        }
        ms.extend(crate::d1::mutants(client, &built.claim, sw, rng).into_iter().map(|(m, f)| (m, f, None, codes.to_vec())));
        ms.extend(header_mutants(&built.claim, sw, rng).into_iter().map(|m| (m, None, None, codes.to_vec())));
        for (m, how) in fact_mutants(built, &an2) {
            let mut m = m;
            m.witness = wb.to_vec();
            ms.push((m, None, Some(how), codes.to_vec()));
        }
    }
    for (n, cs) in code_mutants(codes, rng) {
        ms.push((Mutant { name: n, claim: built.claim.clone(), witness: wb.to_vec(), judge: Judge::Nearcore }, None, None, cs));
    }
    for (m, flags, derived, cs) in ms {
        let (exp, src): (Result<(), String>, String) = match (&m.judge, &flags, derived) {
            (_, _, Some(_)) => (Err("derived: the changed trusted fact changes the main transition".into()), "derived".into()),
            (Judge::Claim, _, _) => (Err("claim-v3 discipline".to_string()), "claim-v3".into()),
            (Judge::Nearcore, None, _) => (judge.judge(ci, client, &m.witness, &cs, rs(&m.claim), None), "nearcore(cold)".into()),
            (Judge::Nearcore, Some(f), _) => (judge.judge(ci, client, &m.witness, &cs, rs(&m.claim), Some(f)), "nearcore(cold,tx_valid=claim)".into()),
        };
        let mname = format!("{name}-{}", m.name);
        let fam = m.name.split(|c: char| c == '.' || c == '(').take(2).collect::<Vec<_>>().join(".");
        d3s.add(&format!("mutant.{fam}.{}", if exp.is_ok() { "accept" } else { "reject" }), 1);
        let meta = json!({
            "case": mname, "kind": "mutant", "mutation": m.name, "base": name,
            "verdict_source": src,
            "nearcore": vstr(&exp),
            "expected_rel": exp.is_ok(),
            "in_d3": true, "expected_rel_d3": exp.is_ok(),
            "in_d2": in_d2, "expected_rel_d2": exp.is_ok() && in_d2,
            "codes": cs.iter().map(|c| { let h = CryptoHash::hash_bytes(c); json!({"hash": h.to_string(), "name": cname(&h), "len": c.len()}) }).collect::<Vec<_>>(),
        });
        stats.mutants += 1;
        write_case(&out.join("mutants").join(&mname), &m.claim, &m.witness, &cs, meta);
    }
}
