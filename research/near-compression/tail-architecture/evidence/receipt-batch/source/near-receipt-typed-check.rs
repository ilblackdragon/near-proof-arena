#[path="support/receipt_arithmetic.rs"] mod receipt;
#[path="support/receipt_outcome_typed.rs"] mod outcome;
#[path="support/tight_sha.rs"] mod tight_sha;
use binius_frontend::CircuitBuilder;
use binius_core::word::Word;
use labinius_binius::{Session,liop::Liop};
use labinius::{Params,Modulus,Opening};
fn main(){
 let raw=std::fs::read(std::env::args().nth(1).unwrap()).unwrap();assert_eq!(&raw[..8],b"NPROU001");let n=u32::from_le_bytes(raw[8..12].try_into().unwrap()) as usize;assert_eq!(raw.len(),12+361*n);
 for shape_index in 0..4 {let shape=outcome::SHAPES[shape_index];
 let b=CircuitBuilder::new();let ins:Vec<_>=(0..35).map(|_|b.add_inout()).collect();
 let x=outcome::Inputs{amounts:core::array::from_fn(|i|[ins[2*i],ins[2*i+1]]),predecessor_len:ins[12],predecessor:ins[13..21].try_into().unwrap(),receiver_len:ins[21],receiver:ins[22..30].try_into().unwrap(),rid:ins[30..34].try_into().unwrap(),height:ins[34]};
 let y=outcome::constrain(&b,&x,shape);let outputs:Vec<_>=(0..10).map(|_|b.add_inout()).collect();
 for (i,w) in [y.arithmetic.after,y.arithmetic.burnt,y.arithmetic.surplus].into_iter().flatten().chain(y.digest).enumerate(){b.assert_eq(format!("out-{i}"),w,outputs[i]);}
 let c=b.build();let log=Liop::new(c.constraint_system().clone()).log_witness_elems();let mut accepted=0;let mut rejected=0;let mut mutations=0;let mut examples=vec![];let mut positive=false;let mut long=false;
 for(index,row)in raw[12..].chunks_exact(361).enumerate(){
  let words:Vec<_>=row[..360].chunks_exact(8).map(|v|Word(u64::from_le_bytes(v.try_into().unwrap()))).collect();let mut w=c.new_witness_filler();for(wire,value)in ins.iter().chain(outputs.iter()).zip(&words){w[*wire]=*value;}
  let ok=c.populate_wire_witness(&mut w).is_ok();let is_refund=words[39].0!=0||words[40].0!=0;let expected=row[360]==1&&is_refund==shape.refund&&(shape.min_receiver..=shape.max_receiver).contains(&(words[21].0 as usize));assert_eq!(ok,expected,"oracle case {index} shape {shape_index}");if !ok{rejected+=1;continue;}accepted+=1;
  let is_positive=words[37].0!=0||words[38].0!=0;let is_long=words[21].0==64;
  if examples.is_empty(){examples.push(w.into_value_vec());positive|=is_positive;long|=is_long;}
  // Each output limb must be linked. Every positive-gas case also tests predecessor classification.
  for j in 0..10{let mut w=c.new_witness_filler();for(wire,value)in ins.iter().chain(outputs.iter()).zip(&words){w[*wire]=*value;}w[outputs[j]]=Word(words[35+j].0^1);assert!(c.populate_wire_witness(&mut w).is_err(),"changed output {index}/{j}");mutations+=1;}
  for at in [12usize,21]{let mut w=c.new_witness_filler();for(wire,value)in ins.iter().chain(outputs.iter()).zip(&words){w[*wire]=*value;}w[ins[at]]=Word(65);assert!(c.populate_wire_witness(&mut w).is_err());mutations+=1;}
 }
 assert!(!examples.is_empty());println!("RECEIPT_OUTCOME shape={shape_index} cases={n} accepted={accepted} rejected={rejected} mutations_rejected={mutations} log_witness={log} shared_arithmetic_hash_wires=true");
 let column=(log as u32).saturating_sub(8).max(1);let params=Params::with_base(log as u32,column,Modulus::Q3889_FS_S,vec![Modulus::Q2917_Q_S,Modulus::Q4861_Q_S,Modulus::Q9721_FS_S,Modulus::Q12637_Q_S],Opening::Recursive).unwrap();let mut session=Session::with_params(c.constraint_system().clone(),params,[0x72;32]);
 for(i,w)in examples.iter().enumerate(){let(proof,_,_)=session.prove(w,None);session.verify(w.inout(),&proof).unwrap();for at in [0usize,37,41]{let mut bad=w.inout().to_vec();bad[at].0^=1;assert!(session.verify(&bad,&proof).is_err());}println!("OUTCOME_PROOF shape={shape_index} example={i} honest=true wrong_input_burn_digest_rejected=true security_claim=false");}
}
}
