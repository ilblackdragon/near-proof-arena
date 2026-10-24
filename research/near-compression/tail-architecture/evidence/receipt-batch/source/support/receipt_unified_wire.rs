//! Fixed-profile trusted-local research packet codec, not arbitrary C network input.
use binius_core::word::Word;
use sha2::{Digest,Sha256};
use labinius::{labrador::{PolxBuf,ProofHandle,sizeof_polx},scheme::{LeftExpansionCommitment,OpeningProof}};
use labinius_binius::{Proof,Opening};
pub const CAP:[usize;1]=[1024];
pub const PUBLIC_BYTES:usize=(3+11*1024)*8;
fn word(x:&[u8])->u64{u64::from_le_bytes(x.try_into().unwrap())}
pub fn outcome_root(public:&[u8],context:&[u8])->Result<[u8;32],String>{
 if public.len()!=PUBLIC_BYTES||context.len()!=24||&public[..24]!=context{return Err("public/context shape".into());}
 let mut leaves=vec![];let mut slot=0;
 for (shape,&cap) in CAP.iter().enumerate(){let mut inactive=false;let mut previous=None;for _ in 0..cap{
  let row=&public[24+88*slot..24+88*(slot+1)];slot+=1;
  if word(&row[..8])==0{inactive=true;if row.iter().any(|b|*b!=0){return Err("inactive row".into());}continue;}
  if inactive||word(&row[..8])!=1||word(&row[8..16])>u32::MAX as u64{return Err("active/index range".into());}
  let id=word(&row[8..16]);if previous.is_some_and(|p|p>=id){return Err("class index order".into());}previous=Some(id);
  let (lo,hi)=(38,133);
  if !(lo..=hi).contains(&word(&row[16..24])){return Err("outcome length class".into());}
  let mut pre=vec![2,0,0,0];pre.extend_from_slice(&row[24..56]);for w in row[56..88].chunks_exact(8){pre.extend_from_slice(&word(w).to_be_bytes());}
  let digest:[u8;32]=Sha256::digest(&pre).into();leaves.push((word(&row[8..16]),digest));
 }}
 leaves.sort_by_key(|x|x.0);for(i,(id,_))in leaves.iter().enumerate(){if *id!=i as u64{return Err("nonconsecutive receipt indices".into());}}
 let mut level:Vec<[u8;32]>=leaves.into_iter().map(|x|x.1).collect();
 while level.len()>1{level=level.chunks(2).map(|p|if p.len()==1{p[0]}else{let mut v=p[0].to_vec();v.extend_from_slice(&p[1]);Sha256::digest(v).into()}).collect();}
 Ok(level.first().copied().unwrap_or([0;32]))
}

/// Active-only encoding. Class is explicit because outcome lengths overlap classes.
pub fn compact(public:&[u8])->Result<Vec<u8>,String>{
 outcome_root(public,public.get(..24).ok_or("public header")?)?;
 let mut rows=vec![];let mut count=0u32;let mut slot=0;
 for(class,&cap)in CAP.iter().enumerate(){for _ in 0..cap{let row=&public[24+88*slot..24+88*(slot+1)];slot+=1;if word(&row[..8])==0{continue;}
  rows.push(class as u8);rows.push(word(&row[16..24]) as u8);rows.extend_from_slice(&(word(&row[8..16]) as u32).to_le_bytes());rows.extend_from_slice(&row[24..56]);for w in row[56..].chunks_exact(8){rows.extend_from_slice(&word(w).to_be_bytes());}count+=1;
 }}
 let mut out=b"NPRCBWU1".to_vec();out.extend_from_slice(&public[..24]);out.extend_from_slice(&count.to_le_bytes());out.extend_from_slice(&rows);
 if expand(&out)?!=public{return Err("noncanonical public vector".into());}Ok(out)
}
pub fn expand(compact:&[u8])->Result<Vec<u8>,String>{
 if compact.len()<36||&compact[..8]!=b"NPRCBWU1"{return Err("public version".into());}
 let count=u32::from_le_bytes(compact[32..36].try_into().unwrap()) as usize;if count>1024||compact.len()!=36+70*count{return Err("public count/length".into());}
 let mut public=vec![0;PUBLIC_BYTES];public[..24].copy_from_slice(&compact[8..32]);let mut used=[0usize;1];let mut previous=None;
 for row in compact[36..].chunks_exact(70){let class=row[0] as usize;if class>=1||used[class]>=CAP[class]{return Err("class capacity".into());}
  let id=u32::from_le_bytes(row[2..6].try_into().unwrap());let key=(class,id);if previous.is_some_and(|p|p>=key){return Err("compact order".into());}previous=Some(key);
  let slot=CAP[..class].iter().sum::<usize>()+used[class];used[class]+=1;let dst=&mut public[24+88*slot..24+88*(slot+1)];dst[..8].copy_from_slice(&1u64.to_le_bytes());dst[8..16].copy_from_slice(&(id as u64).to_le_bytes());dst[16..24].copy_from_slice(&(row[1] as u64).to_le_bytes());dst[24..56].copy_from_slice(&row[6..38]);
  for(i,w)in row[38..].chunks_exact(8).enumerate(){dst[56+8*i..64+8*i].copy_from_slice(&u64::from_be_bytes(w.try_into().unwrap()).to_le_bytes());}
 }
 outcome_root(&public,&compact[8..32])?;Ok(public)
}
struct Reader<'a>{data:&'a[u8],pos:usize}
impl<'a> Reader<'a>{fn take(&mut self,n:usize)->Result<&'a[u8],String>{let end=self.pos.checked_add(n).ok_or("length overflow")?;let x=self.data.get(self.pos..end).ok_or("truncated")?;self.pos=end;Ok(x)}fn part(&mut self)->Result<&'a[u8],String>{let n=usize::try_from(word(self.take(8)?)).map_err(|_|"length overflow")?;self.take(n)}}
/// # Safety
/// Backend bytes must come from trusted local exports. Shape comes from fixed
/// public setup, never from metadata supplied alongside a proof.
pub unsafe fn decode(data:&[u8],context:&[u8],root:&[u8],shape:(usize,usize,usize))->Result<(Vec<Word>,Proof),String>{
 if data.len()>1_000_000{return Err("packet cap".into());}let mut r=Reader{data,pos:0};if r.take(8)?!=b"NPRCBU01"{return Err("version".into());}
 let public=expand(r.part()?)?;if outcome_root(&public,context)?.as_slice()!=root{return Err("wrong outcome root".into());}
 let tape=r.part()?.to_vec();let value=labinius::wire::unpack_f162(r.part()?,1).map_err(|e|format!("{e:?}"))?[0];let left=r.part()?;let tr=r.part()?;let ns=r.part()?;let backend=r.part()?;
 if r.pos!=data.len()||left.len()!=shape.0*sizeof_polx()||tr.len()!=shape.1*sizeof_polx()||ns.len()!=shape.2*8{return Err("trailing/shape".into());}
 let left=PolxBuf::from_bytes(shape.0,left).ok_or("left")?;let tr=PolxBuf::from_bytes(shape.1,tr).ok_or("opening")?;let norms=ns.chunks_exact(8).map(word).collect();
 let handle=ProofHandle::from_local_export(backend)?;if handle.export_bytes()!=backend{return Err("backend roundtrip".into());}
 Ok((public.chunks_exact(8).map(|v|Word(word(v))).collect(),Proof{tape,claimed_value:value,opening:Opening::Recursive{left:LeftExpansionCommitment::from_local_rns(left),proof:OpeningProof::from_local_parts(tr,norms,handle)}}))
}
