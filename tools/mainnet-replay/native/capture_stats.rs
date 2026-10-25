//! Decode capture payloads without opening the node DB. Counts payload contents, not an execution trace.
use near_primitives::{action::Action, receipt::{Receipt, ReceiptEnum}, sharding::ShardChunk,
    stateless_validation::state_witness::ChunkStateWitness, transaction::SignedTransaction};
use serde_json::json;
use std::{collections::BTreeMap, path::Path};
fn inc(m: &mut BTreeMap<String,u64>, k: &str) { *m.entry(k.to_string()).or_default() += 1; }
fn action_name(a: &Action) -> &'static str {
    match a {
        Action::CreateAccount(_) => "CreateAccount", Action::DeployContract(_) => "DeployContract",
        Action::FunctionCall(_) => "FunctionCall", Action::Transfer(_) => "Transfer",
        Action::Stake(_) => "Stake", Action::AddKey(_) => "AddKey", Action::DeleteKey(_) => "DeleteKey",
        Action::DeleteAccount(_) => "DeleteAccount", Action::Delegate(_) => "Delegate",
        Action::DeployGlobalContract(_) => "DeployGlobalContract", Action::UseGlobalContract(_) => "UseGlobalContract",
        Action::DeterministicStateInit(_) => "DeterministicStateInit", Action::TransferToGasKey(_) => "TransferToGasKey",
        Action::WithdrawFromGasKey(_) => "WithdrawFromGasKey", Action::DelegateV2(_) => "DelegateV2",
    }
}
fn actions(xs: &[Action], counts: &mut BTreeMap<String,u64>, methods: &mut BTreeMap<String,u64>) {
    for a in xs { inc(counts, action_name(a)); if let Action::FunctionCall(f) = a { inc(methods, &f.method_name); } }
}
fn delegated(xs: &[Action], counts: &mut BTreeMap<String,u64>, methods: &mut BTreeMap<String,u64>) {
    for a in xs {
        let inner = match a {
            Action::Delegate(d) => d.delegate_action.get_actions(),
            Action::DelegateV2(d) => d.delegate_action.get_actions(),
            _ => continue,
        };
        actions(&inner, counts, methods);
    }
}
fn txs(xs: &[SignedTransaction]) -> serde_json::Value {
    let (mut counts,mut methods)=(BTreeMap::new(),BTreeMap::new());
    let (mut nested,mut nested_methods)=(BTreeMap::new(),BTreeMap::new());
    for t in xs { actions(t.transaction.actions(), &mut counts, &mut methods); delegated(t.transaction.actions(), &mut nested, &mut nested_methods); }
    json!({"count": xs.len(), "actions":counts, "function_methods":methods, "delegate_inner_actions":nested, "delegate_inner_methods":nested_methods})
}
fn receipts<'a>(xs: impl Iterator<Item=&'a Receipt>) -> serde_json::Value {
    let (mut types,mut counts,mut methods)=(BTreeMap::new(),BTreeMap::new(),BTreeMap::new());
    let (mut nested,mut nested_methods)=(BTreeMap::new(),BTreeMap::new());
    let mut ids=std::collections::BTreeSet::new(); let mut n=0;
    for r in xs {
        n+=1; ids.insert(r.receipt_id().to_string());
        let (typ,acts): (&str,&[Action]) = match r.receipt() {
            ReceiptEnum::Action(a) => ("Action",&a.actions), ReceiptEnum::ActionV2(a) => ("ActionV2",&a.actions),
            ReceiptEnum::PromiseYield(a) => ("PromiseYield",&a.actions), ReceiptEnum::PromiseYieldV2(a) => ("PromiseYieldV2",&a.actions),
            ReceiptEnum::Data(_) => ("Data",&[]), ReceiptEnum::PromiseResume(_) => ("PromiseResume",&[]),
            ReceiptEnum::GlobalContractDistribution(_) => ("GlobalContractDistribution",&[]),
        };
        inc(&mut types,typ);actions(acts,&mut counts,&mut methods);delegated(acts,&mut nested,&mut nested_methods);
    }
    json!({"count":n,"unique_ids_within_chunk":ids.len(),"types":types,"actions":counts,"function_methods":methods,"delegate_inner_actions":nested,"delegate_inner_methods":nested_methods})
}
fn main() -> Result<(),Box<dyn std::error::Error>> {
    let root=std::env::args().nth(1).ok_or("usage: w13_capture_stats EXPORTS")?;
    let mut dirs:Vec<_>=std::fs::read_dir(Path::new(&root))?.map(|x| x.map(|e|e.path())).collect::<Result<_,_>>()?;
    dirs.sort();
    for d in dirs {
        if !d.join("capture.json").is_file() {continue;}
        let raw=std::fs::read(d.join("state_witness.borsh"))?;
        let w:ChunkStateWitness=borsh::from_slice(&raw)?;
        let chunk_raw=std::fs::read(d.join("chunk.borsh"))?;
        let c:ShardChunk=borsh::from_slice(&chunk_raw)?;
        assert_eq!(c.chunk_hash(),w.chunk_header().chunk_hash());
        let meta:serde_json::Value=serde_json::from_slice(&std::fs::read(d.join("capture.json"))?)?;
        let implicit:Vec<usize>=w.implicit_transitions().iter().map(|t|t.base_state.len()).collect();
        println!("{}",json!({"capture":d.file_name().unwrap().to_string_lossy(),"height":meta["block_height"],"shard":meta["shard_id"],
            "chunk_hash":w.chunk_header().chunk_hash(),"witness_bytes":raw.len(),"chunk_bytes":chunk_raw.len(),
            "main_proof_entries":w.main_state_transition().base_state.len(),"implicit_proof_entries":implicit,
            "source_receipt_proofs":w.source_receipt_proofs().len(),
            "witness_transactions":txs(w.transactions()),"witness_new_transactions":txs(w.new_transactions()),
            "chunk_transactions":txs(c.to_transactions()),
            "witness_source_receipts":receipts(w.source_receipt_proofs().values().flat_map(|p|p.0.iter())),
            "chunk_prev_outgoing_receipts":receipts(c.prev_outgoing_receipts().iter())}));
    }
    Ok(())
}
