//! Fixed-profile trusted-local research packet codec, not arbitrary C network input.
use binius_core::word::Word;
use sha2::{Digest,Sha256};
use labinius::{labrador::{PolxBuf,ProofHandle,sizeof_polx},scheme::{LeftExpansionCommitment,OpeningProof}};
use labinius_binius::{Proof,Opening};
pub const CAP:[usize;4]=[1024,8,8,8];
pub const PUBLIC_BYTES:usize=(3+11*1048)*8;
fn word(x:&[u8])->u64{u64::from_le_bytes(x.try_into().unwrap())}
pub fn outcome_root(public:&[u8],context:&[u8])->Result<[u8;32],String>{
 if public.len()!=PUBLIC_BYTES||context.len()!=24||&public[..24]!=context{return Err("public/context shape".into());}
 let mut leaves=vec![];let mut slot=0;
 for (shape,&cap) in CAP.iter().enumerate(){let mut inactive=false;let mut previous=None;for _ in 0..cap{
  let row=&public[24+88*slot..24+88*(slot+1)];slot+=1;
  if word(&row[..8])==0{inactive=true;if row.iter().any(|b|*b!=0){return Err("inactive row".into());}continue;}
  if inactive||word(&row[..8])!=1||word(&row[8..16])>u32::MAX as u64{return Err("active/index range".into());}
  let id=word(&row[8..16]);if previous.is_some_and(|p|p>=id){return Err("class index order".into());}previous=Some(id);
  let (lo,hi)=match shape{0=>(38,55),1=>(56,101),2=>(70,119),_=>(120,133)};
  if !(lo..=hi).contains(&word(&row[16..24])){return Err("outcome length class".into());}
  let mut pre=vec![2,0,0,0];pre.extend_from_slice(&row[24..56]);for w in row[56..88].chunks_exact(8){pre.extend_from_slice(&word(w).to_be_bytes());}
  let digest:[u8;32]=Sha256::digest(&pre).into();leaves.push((word(&row[8..16]),digest));
 }}
 leaves.sort_by_key(|x|x.0);for(i,(id,_))in leaves.iter().enumerate(){if *id!=i as u64{return Err("nonconsecutive receipt indices".into());}}
 let mut level:Vec<[u8;32]>=leaves.into_iter().map(|x|x.1).collect();
 while level.len()>1{level=level.chunks(2).map(|p|if p.len()==1{p[0]}else{let mut v=p[0].to_vec();v.extend_from_slice(&p[1]);Sha256::digest(v).into()}).collect();}
 Ok(level.first().copied().unwrap_or([0;32]))
}
struct Reader<'a>{data:&'a[u8],pos:usize}
impl<'a> Reader<'a>{fn take(&mut self,n:usize)->Result<&'a[u8],String>{let end=self.pos.checked_add(n).ok_or("length overflow")?;let x=self.data.get(self.pos..end).ok_or("truncated")?;self.pos=end;Ok(x)}fn part(&mut self)->Result<&'a[u8],String>{let n=usize::try_from(word(self.take(8)?)).map_err(|_|"length overflow")?;self.take(n)}}
/// # Safety
/// Backend bytes must come from trusted local exports. Shape comes from fixed
/// public setup, never from metadata supplied alongside a proof.
pub unsafe fn decode(data:&[u8],context:&[u8],root:&[u8],shape:(usize,usize,usize))->Result<(Vec<Word>,Proof),String>{
 if data.len()>1_000_000{return Err("packet cap".into());}let mut r=Reader{data,pos:0};if r.take(8)?!=b"NPRCBP01"{return Err("version".into());}
 let public=r.part()?;if outcome_root(public,context)?.as_slice()!=root{return Err("wrong outcome root".into());}
 let tape=r.part()?.to_vec();let value=labinius::wire::unpack_f162(r.part()?,1).map_err(|e|format!("{e:?}"))?[0];let left=r.part()?;let tr=r.part()?;let ns=r.part()?;let backend=r.part()?;
 if r.pos!=data.len()||left.len()!=shape.0*sizeof_polx()||tr.len()!=shape.1*sizeof_polx()||ns.len()!=shape.2*8{return Err("trailing/shape".into());}
 let left=PolxBuf::from_bytes(shape.0,left).ok_or("left")?;let tr=PolxBuf::from_bytes(shape.1,tr).ok_or("opening")?;let norms=ns.chunks_exact(8).map(word).collect();
 let handle=ProofHandle::from_local_export(backend)?;if handle.export_bytes()!=backend{return Err("backend roundtrip".into());}
 Ok((public.chunks_exact(8).map(|v|Word(word(v))).collect(),Proof{tape,claimed_value:value,opening:Opening::Recursive{left:LeftExpansionCommitment::from_local_rns(left),proof:OpeningProof::from_local_parts(tr,norms,handle)}}))
}
