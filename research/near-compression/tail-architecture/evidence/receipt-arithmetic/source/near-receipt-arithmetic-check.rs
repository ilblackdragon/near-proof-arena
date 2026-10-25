#[path="support/receipt_arithmetic.rs"] mod receipt;
use binius_frontend::CircuitBuilder;
use binius_core::word::Word;
use labinius_binius::{Session,liop::Liop};
use labinius::{Params,Modulus,Opening};
fn main(){
 let raw=std::fs::read(std::env::args().nth(1).unwrap()).unwrap();assert_eq!(&raw[..8],b"NPRAR001");let n=u32::from_le_bytes(raw[8..12].try_into().unwrap()) as usize;assert_eq!(raw.len(),12+153*n);
 let b=CircuitBuilder::new();let ins:Vec<_>=(0..13).map(|_|b.add_inout()).collect();let pair=|i:usize|[ins[2*i],ins[2*i+1]];
 let x=receipt::Inputs{before:pair(0),deposit:pair(1),locked:pair(2),storage:pair(3),gas_price:pair(4),block_gas_price:pair(5),system:ins[12]};let y=receipt::constrain(&b,&x);
 let outputs:Vec<_>=(0..6).map(|_|b.add_inout()).collect();for (i,w) in [y.after,y.burnt,y.surplus].into_iter().flatten().enumerate(){b.assert_eq(format!("out-{i}"),w,outputs[i]);}
 let c=b.build();let log=Liop::new(c.constraint_system().clone()).log_witness_elems();
 let mut accepted=0;let mut rejected=0;let mut mutations=0;let mut examples=vec![];let mut positive=false;
 for (index,row) in raw[12..].chunks_exact(153).enumerate(){
  let words:Vec<_>=row[..152].chunks_exact(8).map(|v|Word(u64::from_le_bytes(v.try_into().unwrap()))).collect();let expected=row[152]==1;
  let mut w=c.new_witness_filler();for (wire,value) in ins.iter().chain(outputs.iter()).zip(&words){w[*wire]=*value;}
  let ok=c.populate_wire_witness(&mut w).is_ok();assert_eq!(ok,expected,"oracle case {index}");
  if !ok{rejected+=1;continue;}accepted+=1;
  let is_positive=words[15].0!=0||words[16].0!=0;
  if examples.is_empty()||(!positive&&is_positive){examples.push(w.into_value_vec());positive|=is_positive;}
  for j in 0..6{let mut w=c.new_witness_filler();for (wire,value) in ins.iter().chain(outputs.iter()).zip(&words){w[*wire]=*value;}w[outputs[j]]=Word(words[13+j].0^1);assert!(c.populate_wire_witness(&mut w).is_err(),"changed output {index}/{j}");mutations+=1;}
  let mut w=c.new_witness_filler();for (wire,value) in ins.iter().chain(outputs.iter()).zip(&words){w[*wire]=*value;}w[ins[12]]=Word(2);assert!(c.populate_wire_witness(&mut w).is_err());mutations+=1;
 }
 assert!(positive);println!("RECEIPT_ARITHMETIC cases={n} accepted={accepted} rejected={rejected} mutated_outputs_and_system_rejected={mutations} log_witness={log}");
 if log<8{println!("ARITHMETIC_PCS_NOT_RUN reason=below_minimum_geometry required_log_at_least=8 actual_log={log} next=combine_with_outcome_hash");return;}
 // Tiny-shape PCS smoke test only: no security/size/latency inference for NEAR.
 let column=(log as u32).saturating_sub(8).max(1);let params=Params::with_base(log as u32,column,Modulus::Q3889_FS_S,vec![Modulus::Q2917_Q_S,Modulus::Q4861_Q_S,Modulus::Q9721_FS_S,Modulus::Q12637_Q_S],Opening::Recursive).unwrap();let mut session=Session::with_params(c.constraint_system().clone(),params,[0x71;32]);
 for (i,w) in examples.iter().enumerate(){let(proof,_,_)=session.prove(w,None);session.verify(w.inout(),&proof).unwrap();let mut bad=w.inout().to_vec();bad[0].0^=1;assert!(session.verify(&bad,&proof).is_err());let mut bad=w.inout().to_vec();bad[15].0^=1;assert!(session.verify(&bad,&proof).is_err());println!("ARITHMETIC_PROOF example={i} honest=true wrong_input_rejected=true wrong_output_rejected=true security_claim=false");}
}
