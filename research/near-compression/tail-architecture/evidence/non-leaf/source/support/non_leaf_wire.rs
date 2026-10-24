//! Canonical transport for the public job vector; no private data/proof decoding.
use sha2::{Digest,Sha256};
use std::collections::BTreeSet;
const POLICY:&[(usize,usize)]=&[(1,1024),(2,16),(4,8),(8,4),(16,2),(32,1),(2048,1)];
fn bucket(len:usize)->Result<usize,String>{POLICY.iter().position(|p|(len+72)/64<=p.0).ok_or("length exceeds profile".into())}
pub fn expand(wire:&[u8])->Result<Vec<u8>,String>{
 if wire.len()<12||&wire[..8]!=b"NPNOLEF1"{return Err("event version".into());}
 let count=u32::from_le_bytes(wire[8..12].try_into().unwrap()) as usize;
 if count>1056||wire.len()<16+41*count{return Err("event count/length".into());}
 let mut buckets:Vec<Vec<(u32,u32,u8,[u8;32])>>=POLICY.iter().map(|_|vec![]).collect();
 let mut ids=BTreeSet::new();let mut previous=None;
 let end=12+41*count; let leaves=u32::from_le_bytes(wire[end..end+4].try_into().unwrap()) as usize;
 if leaves>1024||wire.len()!=end+4+32*leaves{return Err("receipt count/length".into());}
 for row in wire[12..end].chunks_exact(41){
  let id=u32::from_le_bytes(row[..4].try_into().unwrap());let len=u32::from_le_bytes(row[4..8].try_into().unwrap());let flag=row[8];
  if (id%16==6||id%16==4)||flag>1||!ids.insert(id){return Err("flag/duplicate id".into());}
  let bi=bucket(len as usize)?;let key=(bi,id);
  if previous.is_some_and(|p|p>=key){return Err("noncanonical event order".into());}previous=Some(key);
  if buckets[bi].len()==POLICY[bi].1{return Err("bucket capacity".into());}
  buckets[bi].push((id,len,flag,row[9..].try_into().unwrap()));
 }
 let empty:[u8;32]=Sha256::digest([]).into();
 let mut dense=b"NEARSHATEMPL0001".to_vec();dense.extend_from_slice(&1056u64.to_be_bytes());
 for (i,(_,capacity)) in POLICY.iter().enumerate(){for j in 0..*capacity{
  let (active,tag,digest)=if let Some((id,len,flag,digest))=buckets[i].get(j){(1u64,((*id as u64)<<32)|((*len as u64)<<1)|*flag as u64,*digest)}else{(0,0,empty)};
  dense.extend_from_slice(&active.to_be_bytes());dense.extend_from_slice(&tag.to_be_bytes());dense.extend_from_slice(&digest);
 }}
 Ok(dense)
}
pub fn compact(dense:&[u8],receipts:&[[u8;32]])->Result<Vec<u8>,String>{
 if dense.len()!=50712{return Err("dense event length".into());}
 let mut rows=vec![];let mut count=0u32;
 for row in dense[24..].chunks_exact(48){let active=u64::from_be_bytes(row[..8].try_into().unwrap());
  if active==0{continue;}if active!=1{return Err("active flag".into());}
  let tag=u64::from_be_bytes(row[8..16].try_into().unwrap());let id=(tag>>32) as u32;let len=((tag&0xffff_ffff)>>1) as u32;
  rows.extend_from_slice(&id.to_le_bytes());rows.extend_from_slice(&len.to_le_bytes());rows.push((tag&1) as u8);rows.extend_from_slice(&row[16..]);count+=1;
 }
 let mut wire=b"NPNOLEF1".to_vec();wire.extend_from_slice(&count.to_le_bytes());wire.extend_from_slice(&rows);wire.extend_from_slice(&(receipts.len() as u32).to_le_bytes());for rid in receipts{wire.extend_from_slice(rid);}
 if expand(&wire)?!=dense{return Err("noncanonical dense events".into());}Ok(wire)
}


/// Restore receipt leaves, then use the previously tested full-tree reconstruction.
pub fn full_root(wire:&[u8])->Result<[u8;64],String>{
 expand(wire)?;
 let count=u32::from_le_bytes(wire[8..12].try_into().unwrap()) as usize;let end=12+41*count;
 let mut rows:Vec<Vec<u8>>=wire[12..end].chunks_exact(41).map(|r|r.to_vec()).collect();
 let receipts:Vec<_>=wire[end+4..].chunks_exact(32).collect();
 let mut peos:Vec<_>=rows.iter().filter(|r|u32::from_le_bytes(r[..4].try_into().unwrap())%16==3).cloned().collect();
 peos.sort_by_key(|r|u32::from_le_bytes(r[..4].try_into().unwrap()));
 if peos.len()!=receipts.len(){return Err("PEO/receipt count".into());}
 for (i,(peo,rid)) in peos.iter().zip(receipts).enumerate(){
  if u32::from_le_bytes(peo[..4].try_into().unwrap())!=3+16*i as u32||peo[8]!=1{return Err("PEO association".into());}
  let mut pre=vec![2,0,0,0];pre.extend_from_slice(rid);pre.extend_from_slice(&peo[9..]);
  let digest=Sha256::digest(&pre);let mut row=(4+16*i as u32).to_le_bytes().to_vec();row.extend_from_slice(&68u32.to_le_bytes());row.push(1);row.extend_from_slice(&digest);rows.push(row);
 }
 rows.sort_by_key(|r|{let len=u32::from_le_bytes(r[4..8].try_into().unwrap()) as usize;(bucket(len).unwrap(),u32::from_le_bytes(r[..4].try_into().unwrap()))});
 let mut restored=b"NPNOMRK1".to_vec();restored.extend_from_slice(&(rows.len() as u32).to_le_bytes());for row in rows{restored.extend_from_slice(&row);}
 crate::non_merkle_wire::full_root(&restored)
}
