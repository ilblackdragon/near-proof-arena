//! `mainnet-observables --home HOME --exports EXPORTS --cases CASES --out FILE` (workplan W01).
//!
//! Reads, from a stopped mainnet node's database opened **read-only**, what the node itself stored
//! when it applied each captured witness's main-transition chunk: the execution outcomes
//! (`DBCol::OutcomeIds` + `DBCol::TransactionResultForBlock`, saved because a shard-tracking node
//! has `save_tx_outcomes`), the outgoing receipts (`DBCol::OutgoingReceipts`) and the committed
//! state changes (`DBCol::StateChanges`, `save_state_changes`). The block is the witness's
//! `main_state_transition.block_hash`. `compute_usage` is `#[borsh(skip)]`, so it is not stored and
//! is reported as unknown.
//!
//! One record per case of `CASES` (a replay-case directory per export), in the same JSON form as
//! `observables.rs`, keyed by the sha256 of the case's `claim.bin` and `witness.bin`.

use near_chain::types::ApplyChunkResult;
use near_primitives::stateless_validation::state_witness::ChunkStateWitness;
use near_primitives::transaction::ExecutionOutcomeWithId;
use near_store::adapter::StoreAdapter;
use near_store::{KeyForStateChanges, Mode, NodeStorage, StoreConfig};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::io::Write;
use std::path::PathBuf;

fn sha(b: &[u8]) -> String {
    hex::encode(Sha256::digest(b))
}

pub fn cmd(args: &[String]) -> i32 {
    let arg = |n: &str| -> PathBuf { PathBuf::from(crate::arg(args, n).unwrap_or_else(|| panic!("{n} is required"))) };
    let (home, exports, cases, out) = (arg("--home"), arg("--exports"), arg("--cases"), arg("--out"));
    let cfg = StoreConfig::default();
    let storage = NodeStorage::opener(&home, &cfg, None, None).open_in_mode(Mode::ReadOnly).expect("open node store read-only");
    let store = storage.get_hot_store();
    let cs = store.chain_store();
    let mut names: Vec<String> = std::fs::read_dir(&cases)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().join("claim.bin").exists())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    let mut f = std::io::BufWriter::new(std::fs::File::create(&out).unwrap());
    let (mut ok, mut missing) = (0usize, 0usize);
    for name in &names {
        let claim = std::fs::read(cases.join(name).join("claim.bin")).unwrap();
        let wit = std::fs::read(cases.join(name).join("witness.bin")).unwrap();
        let mut rec = json!({ "case_name": name, "claim_sha256": sha(&claim), "witness_sha256": sha(&wit),
                              "source": "mainnet node store (read-only)" });
        let body = (|| -> Result<serde_json::Value, String> {
            let raw = std::fs::read(exports.join(name).join("state_witness.borsh")).map_err(|e| e.to_string())?;
            let w: ChunkStateWitness = borsh::from_slice(&raw).map_err(|e| e.to_string())?;
            let bh = w.main_state_transition().block_hash;
            let sid = w.chunk_header().shard_id();
            let ids = cs.get_outcomes_by_block_hash_and_shard_id(&bh, sid);
            let mut outs = Vec::new();
            for id in &ids {
                let o = cs.get_outcome_by_id_and_block_hash(id, &bh).ok_or_else(|| format!("outcome {id} not stored"))?;
                outs.push(ExecutionOutcomeWithId { id: *id, outcome: o.outcome });
            }
            if ids.is_empty() && w.chunk_header().prev_outcome_root() != &near_primitives::hash::CryptoHash::default() {
                return Err("outcomes not stored for the main-transition block".into());
            }
            let (root, _) = ApplyChunkResult::compute_outcomes_proof(&outs);
            let receipts = cs.get_outgoing_receipts(&bh, sid).map_err(|e| format!("{e:?}"))?;
            let changes: Vec<_> = KeyForStateChanges::for_block(&bh).find_iter(&store).collect();
            // W01 attribution: each changed key's pre-state value reference, from the witness's
            // own recorded pre-state nodes and the applied chunk's `prev_state_root` (the root its
            // application starts from), both independent of the stored changes.
            let pre_root = cs
                .get_block(&bh)
                .map_err(|e| format!("block: {e:?}"))?
                .chunks()
                .iter_raw()
                .find(|c| c.shard_id() == sid)
                .map(|c| c.prev_state_root())
                .ok_or_else(|| "main-transition chunk header not in block".to_string())?;
            let near_primitives::state::PartialState::TrieValues(nodes) = w.main_state_transition().base_state.clone();
            let pre_trie = near_store::Trie::from_recorded_storage(near_store::PartialStorage { nodes: near_primitives::state::PartialState::TrieValues(nodes) }, pre_root, false);
            let rec_outs: Vec<_> = outs
                .iter()
                .map(|o| {
                    let x = &o.outcome;
                    json!({
                        "id": hex::encode(o.id.0),
                        "executor": hex::encode(x.executor_id.as_bytes()),
                        "status": crate::observables::status_json(&x.status),
                        "gasBurnt": x.gas_burnt.as_gas().to_string(),
                        "tokensBurnt": x.tokens_burnt.as_yoctonear().to_string(),
                        "computeUsage": null,
                        "logs": x.logs.iter().map(|l| hex::encode(l.as_bytes())).collect::<Vec<_>>(),
                        "receiptIds": x.receipt_ids.iter().map(|r| hex::encode(r.0)).collect::<Vec<_>>(),
                    })
                })
                .collect();
            let gas: u64 = outs.iter().map(|o| o.outcome.gas_burnt.as_gas()).sum();
            Ok(json!({
                "status": "ok",
                "height": w.chunk_header().height_included(),
                "shard_id": sid.to_string(),
                "block_hash": hex::encode(bh.0),
                "outcome_root": hex::encode(root.0),
                "header_prev_outcome_root": hex::encode(w.chunk_header().prev_outcome_root().0),
                "gas_used": gas.to_string(),
                "balance_burnt": w.chunk_header().prev_balance_burnt().as_yoctonear().to_string(),
                "balance_burnt_source": "header",
                "compute_usage": null,
                "outcomes": rec_outs,
                "outgoing_receipts": receipts.iter().map(crate::observables::receipt_json).collect::<Vec<_>>(),
                "state_changes": changes.iter().map(|c| crate::observables::change_detail_json(c, Some(&pre_trie))).collect::<Vec<_>>(),
                "store_outcome_ids": ids.iter().map(|i| hex::encode(i.0)).collect::<Vec<_>>(),
            }))
        })();
        match body {
            Ok(serde_json::Value::Object(b)) => {
                ok += 1;
                rec.as_object_mut().unwrap().extend(b);
            }
            Ok(_) => unreachable!(),
            Err(e) => {
                missing += 1;
                rec["status"] = json!(format!("error: {e}"));
            }
        }
        writeln!(f, "{}", serde_json::to_string(&rec).unwrap()).unwrap();
    }
    eprintln!("mainnet-observables: {ok} records, {missing} errors, {} cases", names.len());
    0
}
