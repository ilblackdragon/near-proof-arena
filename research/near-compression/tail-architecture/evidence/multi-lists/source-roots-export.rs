use sha2::{Digest,Sha256};
fn main(){
 let a:Vec<_>=std::env::args().collect();assert_eq!(a.len(),3);
 let cb=std::fs::read(&a[1]).unwrap();
 let p=npudr::v3::d0::prep_claim(&cb).unwrap();
 let roots:Vec<_>=p.lists.iter().enumerate().map(|(i,s)|serde_json::json!({"index":i,"key":s.key,"from_shard":s.from_shard,"root":s.root})).collect();
 let v=serde_json::json!({"claim_sha256":Sha256::digest(&cb).to_vec(),"own":p.h.shard_id,"context":[p.ctx_b2.gas_price as u64,(p.ctx_b2.gas_price>>64) as u64,p.ctx_b2.height,p.h.shard_id],"sources":roots,"witness_loaded":false});
 std::fs::write(&a[2],serde_json::to_vec(&v).unwrap()).unwrap();
}
