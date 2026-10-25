#[path="support/event_wire.rs"] mod event_wire;
use sha2::{Digest,Sha512};
fn main(){
 let dense=std::fs::read(std::env::args().nth(1).unwrap()).unwrap();let wire=event_wire::compact(&dense).unwrap();assert_eq!(event_wire::expand(&wire).unwrap(),dense);
 let mut checks=0;
 let mut reject=|bad:Vec<u8>|{assert!(event_wire::expand(&bad).is_err());checks+=1;};
 let mut bad=wire.clone();bad[0]^=1;reject(bad);
 let mut bad=wire.clone();bad[8..12].copy_from_slice(&3089u32.to_le_bytes());reject(bad);
 let mut bad=wire.clone();bad.pop();reject(bad);
 let mut bad=wire.clone();bad.push(0);reject(bad);
 let mut bad=wire.clone();bad[20]=2;reject(bad);
 let mut bad=wire.clone();bad[16..20].copy_from_slice(&u32::MAX.to_le_bytes());reject(bad);
 let mut bad=wire.clone();bad[53..57].copy_from_slice(&wire[12..16]);reject(bad);
 let mut bad=wire.clone();bad[12..53].copy_from_slice(&wire[53..94]);bad[53..94].copy_from_slice(&wire[12..53]);reject(bad);
 let mut bad=wire.clone();for (i,row) in bad[12..].chunks_exact_mut(41).enumerate(){row[..4].copy_from_slice(&(i as u32).to_le_bytes());row[4..8].fill(0);}reject(bad); // 2460 entries exceed bucket-1 capacity.
 let mut bad=dense.clone();bad[0]^=1;assert!(event_wire::compact(&bad).is_err());checks+=1;
 let mut bad=dense.clone();let off=(24..dense.len()).step_by(48).find(|&i|dense[i..i+8]==[0;8]).unwrap();bad[off+16]^=1;assert!(event_wire::compact(&bad).is_err());checks+=1;
 let mut altered=wire.clone();altered[21]^=1;let altered_dense=event_wire::expand(&altered).unwrap();assert_ne!(Sha512::digest(&dense),Sha512::digest(&altered_dense));checks+=1;
 println!("EVENT_WIRE_CHECK dense={} compact={} checks={checks} roundtrip=true",dense.len(),wire.len());
}
