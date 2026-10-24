#[path="support/receipt_arithmetic.rs"] mod receipt;
#[path="support/receipt_outcome.rs"] mod outcome;
#[path="support/receipt_source.rs"] mod source;
#[path="support/tight_sha.rs"] mod tight_sha;
use binius_frontend::CircuitBuilder;
use binius_core::word::Word;
use labinius_binius::{Session,liop::Liop};
use labinius::{Params,Modulus,Opening};
fn main(){
 let raw=std::fs::read(std::env::args().nth(1).unwrap()).unwrap();assert_eq!(&raw[..8],b"NPRSO001");let n=u32::from_le_bytes(raw[8..12].try_into().unwrap()) as usize;assert_eq!(raw.len(),12+545*n);
 let b=CircuitBuilder::new();let ins:Vec<_>=(0..54).map(|_|b.add_inout()).collect();
 let x=outcome::Inputs{amounts:core::array::from_fn(|i|[ins[2*i],ins[2*i+1]]),predecessor_len:ins[12],predecessor:ins[13..21].try_into().unwrap(),receiver_len:ins[21],receiver:ins[22..30].try_into().unwrap(),rid:ins[30..34].try_into().unwrap(),height:ins[34]};
 let extra=source::Extra{signer_len:ins[35],signer:ins[36..44].try_into().unwrap(),key_kind:ins[44],key:ins[45..53].try_into().unwrap()};
 let bytes=source::serialize(&b.subcircuit("source"),&x,&extra);let list=source::singleton_list(&b.subcircuit("list"),ins[53],bytes);
 let digest=tight_sha::sha256_tight(&b.subcircuit("source-hash"),&list,359);
 let y=outcome::constrain(&b.subcircuit("outcome"),&x);let outputs:Vec<_>=(0..14).map(|_|b.add_inout()).collect();
 for(i,value)in [y.arithmetic.after,y.arithmetic.burnt,y.arithmetic.surplus].into_iter().flatten().chain(y.digest).chain(digest).enumerate(){b.assert_eq(format!("out-{i}"),outputs[i],value);}
 let c=b.build();let log=Liop::new(c.constraint_system().clone()).log_witness_elems();let(mut accepted,mut rejected,mut mutations)=(0,0,0);let mut examples=vec![];let mut have_key1=false;let mut have_max=false;
 for(index,row)in raw[12..].chunks_exact(545).enumerate(){
  let words:Vec<_>=row[..544].chunks_exact(8).map(|x|Word(u64::from_le_bytes(x.try_into().unwrap()))).collect();
  let fill=|change:Option<usize>|{let mut w=c.new_witness_filler();for(i,wire)in ins.iter().chain(outputs.iter()).enumerate(){w[*wire]=Word(words[i].0^u64::from(change==Some(i)));}w};
  let mut w=fill(None);let ok=c.populate_wire_witness(&mut w).is_ok();assert_eq!(ok,row[544]==1,"case {index}");if !ok{rejected+=1;continue;}accepted+=1;
  let key1=words[44].0==1;let max=words[12].0==64&&words[21].0==64&&words[35].0==64;
  if examples.is_empty()||(!have_key1&&key1)||(!have_max&&max){examples.push(w.into_value_vec());have_key1|=key1;have_max|=max;}
  // Change all computed outputs and a used byte of every source input field.
  for at in (54..68).chain([2,8,12,13,21,22,30,35,36,44,45,53]){let mut w=fill(Some(at));assert!(c.populate_wire_witness(&mut w).is_err(),"mutation {index}/{at}");mutations+=1;}
 }
 println!("RECEIPT_SOURCE cases={n} accepted={accepted} rejected={rejected} mutations={mutations} log={log} same_source_outcome_wires=true");
 let params=Params::with_base(log as u32,(log as u32).saturating_sub(8).max(1),Modulus::Q3889_FS_S,vec![Modulus::Q2917_Q_S,Modulus::Q4861_Q_S,Modulus::Q9721_FS_S,Modulus::Q12637_Q_S],Opening::Recursive).unwrap();let mut session=Session::with_params(c.constraint_system().clone(),params,[0x75;32]);
 for(i,w)in examples.iter().enumerate(){let(proof,_,_)=session.prove(w,None);session.verify(w.inout(),&proof).unwrap();for at in [2usize,53,60,64]{let mut bad=w.inout().to_vec();bad[at].0^=1;assert!(session.verify(&bad,&proof).is_err());}println!("RECEIPT_SOURCE_PROOF example={i} honest=true public_mutations_rejected=4 full_near=false");}
}
