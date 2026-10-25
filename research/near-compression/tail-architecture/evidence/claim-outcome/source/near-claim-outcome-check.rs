#[path="support/event_wire.rs"] mod full_event_wire;
#[path="support/non_merkle_wire.rs"] mod non_merkle_wire;
#[path="support/non_leaf_wire.rs"] mod event_wire;
#[path="support/claim_outcome.rs"] mod claim_outcome;
fn main(){
 let a:Vec<_>=std::env::args().collect();let claims=std::path::Path::new(&a[1]);let fixtures=std::path::Path::new(&a[2]);let mut cases=0;let mut negative=0;let mut scope=0;
 for entry in std::fs::read_dir(claims).unwrap(){let path=entry.unwrap().path();let file=fixtures.join(path.file_name().unwrap()).with_extension("wire");if !file.exists(){continue;}
  let claim=std::fs::read(path.join("claim.bin")).unwrap();let wire=std::fs::read(file).unwrap();claim_outcome::check(&wire,&claim).unwrap();cases+=1;
  let mut at=0;for _ in 0..2{let n=u32::from_le_bytes(claim[at..at+4].try_into().unwrap()) as usize;at+=4+n;}let version=at;at+=4;
  let n=u32::from_le_bytes(claim[at..at+4].try_into().unwrap()) as usize;at+=4+n+32+4;let root_at=at+65;
  let mut bad=claim.clone();bad[root_at]^=1;assert!(claim_outcome::check(&wire,&bad).is_err());negative+=1;
  let mut bad=claim.clone();bad[4]^=1;assert!(claim_outcome::check(&wire,&bad).is_err());negative+=1;
  let mut bad=claim.clone();bad[version]^=1;assert!(claim_outcome::check(&wire,&bad).is_err());negative+=1;
  assert!(claim_outcome::check(&wire,&claim[..root_at+31]).is_err());negative+=1;
  let count=u32::from_le_bytes(wire[8..12].try_into().unwrap()) as usize;let end=12+41*count;
  if wire.len()>end+4{let mut bad=wire.clone();bad[end+4]^=1;assert!(claim_outcome::check(&bad,&claim).is_err());negative+=1;}
  // Demonstrate the scope limit: changing a state root leaves this partial relation true.
  let mut different_state=claim.clone();different_state[root_at-32]^=1;assert!(claim_outcome::check(&wire,&different_state).is_ok());scope+=1;
 }
 assert_eq!(cases,64);println!("CLAIM_OUTCOME_CHECK cases={cases} rejected_mutations={negative} unrelated_state_changes_not_checked={scope} full_near_validity=false");
}
