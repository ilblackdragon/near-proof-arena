use std::{path::PathBuf,time::Instant};
use sha2::{Digest,Sha256};
fn main(){
 let a:Vec<String>=std::env::args().collect();assert_eq!(a.len(),3);
 let case=PathBuf::from(&a[1]);let out=PathBuf::from(&a[2]);std::fs::create_dir_all(&out).unwrap();
 let cb=std::fs::read(case.join("claim.bin")).unwrap();let wb=std::fs::read(case.join("witness.bin")).unwrap();
 let t=Instant::now();let ci=npudr::v3::prove::case_inputs(&cb,&wb,None).unwrap();let elapsed=t.elapsed().as_secs_f64();
 std::fs::write(out.join("rcpt.json"),&ci.entries["rcpt"]).unwrap();
 for name in ["sha_t","sha_r"]{
  let text=&ci.entries[name];let messages:Vec<npudr::v3::sha::ShaMsg>=serde_json::from_str(text).unwrap();
  let mut wire=b"NPSHA001".to_vec();wire.extend_from_slice(&(messages.len() as u32).to_le_bytes());
  let mut bytes=0;let mut blocks=0;
  for m in &messages{wire.extend_from_slice(&m.id.to_le_bytes());wire.extend_from_slice(&(m.bytes.len() as u32).to_le_bytes());wire.push(m.dmult as u8);wire.extend_from_slice(&Sha256::digest(&m.bytes));wire.extend_from_slice(&m.bytes);bytes+=m.bytes.len();blocks+=(m.bytes.len()+9).div_ceil(64);}
  std::fs::write(out.join(format!("{name}.batch")),&wire).unwrap();std::fs::write(out.join(format!("{name}.json")),text).unwrap();
  println!("{}",serde_json::json!({"family":name,"messages":messages.len(),"message_bytes":bytes,"sha256_compressions":blocks,"export_bytes":wire.len(),"native_entries_s":elapsed}));
 }
}
