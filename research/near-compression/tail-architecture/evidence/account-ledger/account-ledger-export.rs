use std::path::PathBuf;
use sha2::{Digest,Sha256};
use npudr::{v3::{d0::walk_d0,hint::{decode_w,get},rcptfam::native},near::spec::account_key_path};
fn main(){
 let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),3);let case=PathBuf::from(&a[1]);
 let cb=std::fs::read(case.join("claim.bin")).unwrap();let wb=std::fs::read(case.join("witness.bin")).unwrap();
 let walk=walk_d0(&cb).unwrap();let w=decode_w(&wb).unwrap();let n=native(&cb,&wb).unwrap();
 let mut seen=std::collections::BTreeSet::new();let mut accounts=vec![];
 for r in n.rs(){if seen.insert(r.receiver_id.clone()){
  let key=account_key_path(&r.receiver_id);let initial=get(&n.pre,&key).unwrap();let final_value=get(&n.post,&key).unwrap();
  accounts.push(serde_json::json!({"receiver":r.receiver_id,"initial":initial,"final":final_value}));
 }}
 let v=serde_json::json!({"status":"TRUSTED_NATIVE_STATE_READS_NOT_SUCCINCT_AUTHENTICATION","claim_sha256":Sha256::digest(&cb).to_vec(),"witness_sha256":Sha256::digest(&wb).to_vec(),"pre_state_root":walk.slot_b2.prev_state_root,"accounts":accounts,"all_main_value_count":w.main.values.len(),"all_main_value_bytes":w.main.values.iter().map(|v|v.len()).sum::<usize>()});
 std::fs::write(&a[2],serde_json::to_vec(&v).unwrap()).unwrap();
}
