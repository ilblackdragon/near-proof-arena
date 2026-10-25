use std::{path::PathBuf,time::Instant};
use sha2::{Digest,Sha256};
use npudr::v3::{d0::prep_claim,hint::decode_w};
fn main(){
 let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),3);
 let case=PathBuf::from(&a[1]);let out=PathBuf::from(&a[2]);
 let cb=std::fs::read(case.join("claim.bin")).unwrap();let wb=std::fs::read(case.join("witness.bin")).unwrap();
 let t=Instant::now();let p=prep_claim(&cb).unwrap();let claim_s=t.elapsed().as_secs_f64();
 let w=decode_w(&wb).unwrap();let mut rows=Vec::new();
 for (j,s) in p.lists.iter().enumerate(){
  let e=w.entries.iter().rev().find(|e|e.key==s.key).unwrap();
  let mut raw=e.to_shard.to_le_bytes().to_vec();raw.extend(npudr::near::spec::encode_receipts(&e.receipts));
  rows.push(serde_json::json!({"index":j,"key":s.key,"expected_from_shard":s.from_shard,"expected_root":s.root,
   "from_shard":e.from_shard,"to_shard":e.to_shard,"count":e.receipts.len(),"source_bytes":raw.len(),"source_sha256":Sha256::digest(&raw).to_vec(),
   "path":e.path.iter().map(|(s,d)|serde_json::json!({"sibling":s,"direction":d})).collect::<Vec<_>>()}));
 }
 let value=serde_json::json!({"status":"NATIVE_CLAIM_DERIVATION_NOT_SUCCINCT_PROOF","claim_sha256":Sha256::digest(&cb).to_vec(),"witness_sha256":Sha256::digest(&wb).to_vec(),"claim_prepare_s":claim_s,"own":p.h.shard_id,"entry_keys":w.entries.iter().map(|e|&e.key).collect::<Vec<_>>(),"sources":rows});
 std::fs::write(out,serde_json::to_vec(&value).unwrap()).unwrap();
}
