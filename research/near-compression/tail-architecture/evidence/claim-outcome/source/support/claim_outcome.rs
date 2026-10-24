//! Public outcome-root linkage only. This is NOT a full NEAR claim decoder/checker.
use sha2::{Digest,Sha256};
struct Reader<'a>{b:&'a[u8],p:usize}
impl<'a> Reader<'a>{
 fn take(&mut self,n:usize)->Result<&'a[u8],String>{let end=self.p.checked_add(n).ok_or("length overflow")?;let x=self.b.get(self.p..end).ok_or("truncated claim prefix")?;self.p=end;Ok(x)}
 fn bytes(&mut self)->Result<&'a[u8],String>{let n=u32::from_le_bytes(self.take(4)?.try_into().unwrap()) as usize;self.take(n)}
}
/// Extract one public field from the caller's statement. Remaining claim fields
/// and the rest of the chunk header MUST be validated by the full NEAR relation.
pub fn expected_root(claim:&[u8])->Result<[u8;32],String>{
 if claim.len()>16*1024*1024{return Err("claim cap".into());}
 let mut r=Reader{b:claim,p:0};
 if r.bytes()?!=b"near-arena-claim-v3"||r.bytes()?!=b"near/pv86/chunk-validation/v0"{return Err("claim/statement tag".into());}
 if u32::from_le_bytes(r.take(4)?.try_into().unwrap())!=86{return Err("protocol version".into());}
 r.bytes()?;r.take(32)?;let inner=r.bytes()?;
 if inner.len()<97||!matches!(inner[0],3|4){return Err("chunk inner prefix".into());}
 Ok(inner[65..97].try_into().unwrap())
}
/// The caller also verifies the proof over event_wire::expand(wire), and the
/// complete job root. This function alone does not authenticate PEO digests.
pub fn derived_root(wire:&[u8])->Result<[u8;32],String>{
 crate::event_wire::full_root(wire)?; // canonical records, exact PEO pairing/count
 let n=u32::from_le_bytes(wire[8..12].try_into().unwrap()) as usize;let end=12+41*n;
 let mut peos:Vec<_>=wire[12..end].chunks_exact(41).filter(|r|u32::from_le_bytes(r[..4].try_into().unwrap())%16==3).collect();
 peos.sort_by_key(|r|u32::from_le_bytes(r[..4].try_into().unwrap()));
 let mut level:Vec<[u8;32]>=peos.iter().zip(wire[end+4..].chunks_exact(32)).map(|(peo,rid)|{let mut pre=vec![2,0,0,0];pre.extend_from_slice(rid);pre.extend_from_slice(&peo[9..]);Sha256::digest(pre).into()}).collect();
 while level.len()>1{level=level.chunks(2).map(|p|if p.len()==1{p[0]}else{let mut pre=[0;64];pre[..32].copy_from_slice(&p[0]);pre[32..].copy_from_slice(&p[1]);Sha256::digest(pre).into()}).collect();}
 Ok(level.first().copied().unwrap_or([0;32]))
}
pub fn check(wire:&[u8],claim:&[u8])->Result<(),String>{if derived_root(wire)?!=expected_root(claim)?{return Err("claim outcome root mismatch".into());}Ok(())}
pub fn packet_public(packet:&[u8])->Result<&[u8],String>{
 if packet.len()<16||&packet[..8]!=b"NPNOLEF2"{return Err("packet prefix".into());}
 let n=usize::try_from(u64::from_le_bytes(packet[8..16].try_into().unwrap())).map_err(|_|"public length")?;
 packet.get(16..16usize.checked_add(n).ok_or("public length overflow")?).ok_or("truncated packet public section".into())
}
