//! Trusted-local decoder; expected bytes are independently supplied.
use binius_core::word::Word;
use labinius::{labrador::{PolxBuf,ProofHandle,sizeof_polx},scheme::{LeftExpansionCommitment,OpeningProof}};
use labinius_binius::{Proof,Opening};
fn word(x:&[u8])->u64{u64::from_le_bytes(x.try_into().unwrap())}
struct Reader<'a>{data:&'a[u8],pos:usize}
impl<'a> Reader<'a>{fn take(&mut self,n:usize)->Result<&'a[u8],String>{let end=self.pos.checked_add(n).ok_or("length overflow")?;let x=self.data.get(self.pos..end).ok_or("truncated")?;self.pos=end;Ok(x)}fn part(&mut self)->Result<&'a[u8],String>{let n=usize::try_from(word(self.take(8)?)).map_err(|_|"length overflow")?;self.take(n)}}
/// # Safety
/// Backend bytes must come from trusted local exports. Shape comes from fixed
/// public setup, never from metadata supplied alongside a proof.
pub unsafe fn decode(data:&[u8],expected:&[u8],shape:(usize,usize,usize),caps:&[usize],mode:u32,account_slots:usize)->Result<(Vec<Word>,Proof),String>{
 if data.len()>1_000_000{return Err("packet cap".into());}let mut r=Reader{data,pos:0};if r.take(8)?!=b"NPMULT02"{return Err("version".into());}
 let count=u32::from_le_bytes(r.take(4)?.try_into().unwrap()) as usize;if count!=caps.len(){return Err("wrong list profile count".into());}
 for &cap in caps{let declared=u32::from_le_bytes(r.take(4)?.try_into().unwrap()) as usize;if declared!=cap{return Err("wrong list capacity".into());}}
 let declared_mode=u32::from_le_bytes(r.take(4)?.try_into().unwrap());if declared_mode!=mode{return Err("wrong profile mode".into());}
 let declared_slots=u32::from_le_bytes(r.take(4)?.try_into().unwrap()) as usize;if declared_slots!=account_slots{return Err("wrong account table size".into());}

 let public=r.part()?.to_vec();if public!=expected||public.len()%8!=0{return Err("wrong expected public statement".into());}
 let tape=r.part()?.to_vec();let value=labinius::wire::unpack_f162(r.part()?,1).map_err(|e|format!("{e:?}"))?[0];let left=r.part()?;let tr=r.part()?;let ns=r.part()?;let backend=r.part()?;
 if r.pos!=data.len()||left.len()!=shape.0*sizeof_polx()||tr.len()!=shape.1*sizeof_polx()||ns.len()!=shape.2*8{return Err("trailing/shape".into());}
 let left=PolxBuf::from_bytes(shape.0,left).ok_or("left")?;let tr=PolxBuf::from_bytes(shape.1,tr).ok_or("opening")?;let norms=ns.chunks_exact(8).map(word).collect();
 let handle=ProofHandle::from_local_export(backend)?;if handle.export_bytes()!=backend{return Err("backend roundtrip".into());}
 Ok((public.chunks_exact(8).map(|v|Word(word(v))).collect(),Proof{tape,claimed_value:value,opening:Opening::Recursive{left:LeftExpansionCommitment::from_local_rns(left),proof:OpeningProof::from_local_parts(tr,norms,handle)}}))
}
