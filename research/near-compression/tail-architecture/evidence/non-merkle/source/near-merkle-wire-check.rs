#[path="support/event_wire.rs"] mod full_event_wire;
#[path="support/non_merkle_wire.rs"] mod event_wire;
fn main(){
 let dir=std::path::PathBuf::from(std::env::args().nth(1).unwrap());let mut cases=0;let mut negative=0;
 for p in std::fs::read_dir(&dir).unwrap(){let p=p.unwrap().path();if p.extension().is_none_or(|x|x!="wire"){continue;}
  let wire=std::fs::read(&p).unwrap();let root=std::fs::read(p.with_extension("root")).unwrap();
  assert_eq!(event_wire::full_root(&wire).unwrap().as_slice(),root);let dense=event_wire::expand(&wire).unwrap();assert_eq!(event_wire::compact(&dense).unwrap(),wire);cases+=1;
  let leaf=wire[12..].chunks_exact(41).position(|r|u32::from_le_bytes(r[..4].try_into().unwrap())%16==4);
  if let Some(i)=leaf{let off=12+41*i;
   let wrong=|bad:&[u8]|{assert!(match event_wire::full_root(bad){Err(_)=>true,Ok(r)=>r.as_slice()!=root});};
   let mut bad=wire.clone();bad[off+9]^=1;wrong(&bad);negative+=1;
   let mut bad=wire.clone();bad[off+8]=0;wrong(&bad);negative+=1;
   let mut bad=wire.clone();bad[off..off+4].copy_from_slice(&6u32.to_le_bytes());wrong(&bad);negative+=1;
   let mut bad=wire.clone();bad.drain(off..off+41);let n=u32::from_le_bytes(wire[8..12].try_into().unwrap())-1;bad[8..12].copy_from_slice(&n.to_le_bytes());wrong(&bad);negative+=1;
  }
 }
 assert!(cases>=64);println!("MERKLE_WIRE_CHECK cases={cases} negative_checks={negative} exact_original_roots=true");
}
