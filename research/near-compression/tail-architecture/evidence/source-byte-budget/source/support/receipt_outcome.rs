//! Shared-wire transfer arithmetic -> partial outcome serialization -> SHA256.
//! This kernel does not prove source/state membership or full receipt validity.
use binius_frontend::{CircuitBuilder,Wire};
use binius_circuits::fixed_byte_vec::ByteVec;
use crate::{receipt,tight_sha};
pub struct Inputs{pub amounts:[receipt::U128;6],pub predecessor_len:Wire,pub predecessor:[Wire;8],pub receiver_len:Wire,pub receiver:[Wire;8],pub rid:[Wire;4],pub height:Wire}
pub struct Outputs{pub arithmetic:receipt::Outputs,pub digest:[Wire;4]}
fn byte(b:&CircuitBuilder,w:Wire,i:usize)->Wire{b.band(b.shr(w,(8*i) as u32),b.add_constant_64(255))}
fn pack(b:&CircuitBuilder,bytes:&[Wire])->Vec<Wire>{bytes.chunks(8).map(|chunk|{let mut w=b.add_constant_64(0);for(i,x)in chunk.iter().enumerate(){w=b.bor(w,b.shl(*x,(8*i) as u32));}w}).collect()}
pub fn constrain(b:&CircuitBuilder,x:&Inputs)->Outputs{
 let zero=b.add_constant_64(0);
 for (name,len) in [("predecessor",x.predecessor_len),("receiver",x.receiver_len)]{
  b.assert_false(format!("{name}-too-long"),b.icmp_ugt(len,b.add_constant_64(64)));
  b.assert_non_zero(format!("{name}-empty"),len);
 }
 let sys_word=u64::from_le_bytes(*b"system\0\0");
 let sys=b.band(b.icmp_eq(x.predecessor_len,b.add_constant_64(6)),b.icmp_eq(b.band(x.predecessor[0],b.add_constant_64((1<<48)-1)),b.add_constant_64(sys_word)));
 let a=&x.amounts;let arithmetic=receipt::constrain(&b.subcircuit("arithmetic"),&receipt::Inputs{before:a[0],deposit:a[1],locked:a[2],storage:a[3],gas_price:a[4],block_gas_price:a[5],system:b.shr(sys,63)});
 let refund=b.icmp_ne(b.bor(arithmetic.surplus[0],arithmetic.surplus[1]),zero);
 let mut rid_pre=x.rid.to_vec();rid_pre.push(x.height);rid_pre.push(zero);
 let refund_digest=tight_sha::sha256_tight(&b.subcircuit("refund-id"),&ByteVec::new(rid_pre,b.add_constant_64(48)),48);
 // The two encodings share the SAME constrained burnt wires, not copied host values.
 let branch=|has_refund:bool|->Vec<Wire>{
  let extra=if has_refund{32}else{0};let base=32+extra;let mut out=vec![];
  for j in 0..133{
   let mut v=zero;
   if j==0{v=b.add_constant_64(has_refund as u64);}
   else if has_refund&&(4..36).contains(&j){let k=j-4;v=byte(b,refund_digest[k/8],7-k%8);}
   else if (4+extra..12+extra).contains(&j){v=b.add_constant_64((223_182_562_500u64>>(8*(j-4-extra)))&255);}
   else if (12+extra..28+extra).contains(&j){let k=j-12-extra;v=byte(b,arithmetic.burnt[k/8],k%8);}
   else if (28+extra..32+extra).contains(&j){v=byte(b,x.receiver_len,j-28-extra);}
   else if (base..base+64).contains(&j){let k=j-base;v=b.select(b.icmp_ult(b.add_constant_64(k as u64),x.receiver_len),byte(b,x.receiver[k/8],k%8),zero);}
   if j>=base&&j<=base+64{v=b.select(b.icmp_eq(x.receiver_len,b.add_constant_64((j-base) as u64)),b.add_constant_64(2),v);}
   out.push(v);
  }out
 };
 let no=branch(false);let yes=branch(true);let bytes:Vec<_>=no.into_iter().zip(yes).map(|(no,yes)|b.select(refund,yes,no)).collect();
 let(offset,_)=b.iadd(x.receiver_len,b.select(refund,b.add_constant_64(69),b.add_constant_64(37)));
 let digest=tight_sha::sha256_tight(&b.subcircuit("outcome-hash"),&ByteVec::new(pack(b,&bytes),offset),133);
 Outputs{arithmetic,digest}
}
