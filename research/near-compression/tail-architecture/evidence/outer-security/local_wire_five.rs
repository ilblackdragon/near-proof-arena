//! Local research file reconstruction. Not an untrusted proof decoding API.
use binius_core::word::Word;
use labinius::{labrador::{PolxBuf,ProofHandle,sizeof_polx},scheme::{LeftExpansionCommitment,OpeningProof}};
use labinius_binius::{Proof,Opening};
struct Reader<'a>{data:&'a[u8],pos:usize}
impl<'a> Reader<'a>{fn take(&mut self,n:usize)->Result<&'a[u8],String>{let end=self.pos.checked_add(n).ok_or("length overflow")?;let x=self.data.get(self.pos..end).ok_or("truncated")?;self.pos=end;Ok(x)}fn part(&mut self)->Result<&'a[u8],String>{let n=u64::from_le_bytes(self.take(8)?.try_into().unwrap());let n=usize::try_from(n).map_err(|_|"length overflow")?;self.take(n)}}
/// # Safety
/// The backend and RNS sections must originate from the trusted local exporter.
/// Bounds on parsing alone do not make the upstream C verifier adversarial-safe.
pub unsafe fn decode(data:&[u8],expected:&[u8])->Result<(Vec<Word>,Proof),String>{
 if data.len()>1_000_000{return Err("packet cap".into());}let mut r=Reader{data,pos:0};if r.take(8)?!=b"NPTMPL01"{return Err("version".into());}
 let public=r.part()?;if public.len()!=64||public!=expected{return Err("wrong expected root".into());}
 let tape=r.part()?.to_vec();let value=labinius::wire::unpack_f162(r.part()?,1).map_err(|e|format!("{e:?}"))?[0];
 let left=r.part()?;let tr=r.part()?;let ns=r.part()?;let backend=r.part()?;if r.pos!=data.len(){return Err("trailing bytes".into());}
 // This binary's fixed capacity template; check before allocating RNS buffers.
 if left.len()!=5*sizeof_polx()||tr.len()!=11*sizeof_polx()||ns.len()!=36*8{return Err("template opening shape".into());}
 let left=PolxBuf::from_bytes(5,left).ok_or("left")?;let tr=PolxBuf::from_bytes(11,tr).ok_or("opening")?;
 let norms=ns.chunks_exact(8).map(|v|u64::from_le_bytes(v.try_into().unwrap())).collect();
 let handle=ProofHandle::from_local_export(backend)?;
 if handle.export_bytes()!=backend{return Err("backend roundtrip not byte-identical".into());}
 let proof=Proof{tape,claimed_value:value,opening:Opening::Recursive{left:LeftExpansionCommitment::from_local_rns(left),proof:OpeningProof::from_local_parts(tr,norms,handle)}};
 let public=public.chunks_exact(8).map(|v|Word(u64::from_be_bytes(v.try_into().unwrap()))).collect();Ok((public,proof))
}
