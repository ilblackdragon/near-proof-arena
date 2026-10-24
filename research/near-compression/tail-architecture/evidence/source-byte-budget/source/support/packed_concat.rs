//! Exact packed-byte concatenation by canonical masking and barrel shifts.
//! No prover-selected offsets or probabilistic equality fingerprints.
use binius_frontend::{CircuitBuilder,Wire};
use binius_circuits::{fixed_byte_vec::ByteVec,shift::{var_sll_bytes,var_srl_bytes}};
struct Canonical(ByteVec);
fn clean(b:&CircuitBuilder,v:&ByteVec)->Canonical{
 let lo=*v.len_range.start();let hi=*v.len_range.end();assert!(hi<=v.data.len()*8);
 let zero=b.add_constant_64(0);let all=b.add_constant_64(u64::MAX);
 b.assert_false("below-length-range",b.icmp_ult(v.len_bytes,b.add_constant_64(lo as u64)));
 b.assert_false("above-length-range",b.icmp_ugt(v.len_bytes,b.add_constant_64(hi as u64)));
 let data=if lo==hi{v.data[..hi.div_ceil(8)].iter().enumerate().map(|(i,&w)|{
  if (i+1)*8<=hi{w}else{b.band(w,b.add_constant_64((1u64<<(8*(hi%8)))-1))}
 }).collect()}else{
  let words=b.shr(v.len_bytes,3);let rem=b.band(v.len_bytes,b.add_constant_64(7));let mask=b.bxor(var_sll_bytes(b,all,rem),all);
  v.data[..hi.div_ceil(8)].iter().enumerate().map(|(i,&w)|{let at=b.add_constant_64(i as u64);b.select(b.icmp_ult(at,words),w,b.select(b.icmp_eq(at,words),b.band(w,mask),zero))}).collect()
 };
 Canonical(ByteVec::new_with_len_range(data,v.len_bytes,lo..=hi))
}
fn pair(b:&CircuitBuilder,a:Canonical,c:Canonical)->Canonical{
 let a=a.0;let c=c.0;let amin=*a.len_range.start();let amax=*a.len_range.end();let lo=amin+c.len_range.start();let hi=amax+c.len_range.end();let n=hi.div_ceil(8);let zero=b.add_constant_64(0);
 let mut shifted:Vec<Wire>;
 if amin==amax{
  let off=amin/8;let rem=amin%8;
  shifted=(0..n).map(|i|{if i<off{return zero;}let j=i-off;let w=c.data.get(j).copied().unwrap_or(zero);if rem==0{return w;}let prev=if j==0{zero}else{c.data.get(j-1).copied().unwrap_or(zero)};b.bxor(b.shl(w,(rem*8) as u32),b.shr(prev,((8-rem)*8) as u32))}).collect();
 }else{
  let rem=b.band(a.len_bytes,b.add_constant_64(7));let neg=b.band(b.isub_bin_bout(zero,rem,zero).0,b.add_constant_64(7));let aligned=b.icmp_eq(rem,zero);
  shifted=(0..n).map(|i|{let current=c.data.get(i).copied().unwrap_or(zero);let prev=if i==0{zero}else{c.data.get(i-1).copied().unwrap_or(zero)};let carry=b.select(aligned,zero,var_srl_bytes(b,prev,neg));b.bxor(var_sll_bytes(b,current,rem),carry)}).collect();
  let words=b.shr(a.len_bytes,3);let mut bit=0;while (1usize<<bit)<=amax/8{
   let step=1usize<<bit;let condition=b.shl(b.band(b.shr(words,bit as u32),b.add_constant_64(1)),63);
   shifted=(0..n).map(|i|b.select(condition,if i>=step{shifted[i-step]}else{zero},shifted[i])).collect();bit+=1;
  }
 }
 let data=shifted.into_iter().enumerate().map(|(i,w)|b.bxor(a.data.get(i).copied().unwrap_or(zero),w)).collect();
 let len=if amin==amax&&c.len_range.start()==c.len_range.end(){b.add_constant_64(hi as u64)}else{b.iadd(a.len_bytes,c.len_bytes).0};
 Canonical(ByteVec::new_with_len_range(data,len,lo..=hi))
}
pub fn concat(b:&CircuitBuilder,inputs:&[ByteVec])->ByteVec{
 if inputs.is_empty(){return ByteVec::new_const_len(b,vec![],0);}
 let mut parts:Vec<_>=inputs.iter().enumerate().map(|(i,v)|clean(&b.subcircuit(format!("clean-{i}")),v)).collect();let mut level=0;
 while parts.len()>1{let mut next=vec![];let mut it=parts.into_iter();let mut i=0;while let Some(a)=it.next(){next.push(if let Some(c)=it.next(){pair(&b.subcircuit(format!("join-{level}-{i}")),a,c)}else{a});i+=1;}parts=next;level+=1;}
 parts.pop().unwrap().0
}
