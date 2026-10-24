use std::{io::{Cursor,Read},time::Instant};
use sha2::{Digest,Sha256,Sha512};
use binius_core::word::Word;
use binius_frontend::{CircuitBuilder,Wire};
use binius_circuits::{sha256::sha256_fixed,sha512::sha512_fixed};
use labinius_binius::{Session,Opening,liop::Liop};
use labinius::{Params,Opening as PcsOpening,scheme::SUITES};
use labinius_bench::pin;
struct Message {id:u32,flag:u8,bytes:Vec<u8>,digest:[u8;32]}
fn u32le(r:&mut Cursor<Vec<u8>>)->u32{let mut b=[0;4];r.read_exact(&mut b).unwrap();u32::from_le_bytes(b)}
fn pack32(b:&[u8])->Vec<u64>{b.chunks(4).map(|x|{let mut a=[0u8;4];a[..x.len()].copy_from_slice(x);u32::from_be_bytes(a) as u64}).collect()}
fn main(){
 pin(8);let args:Vec<_>=std::env::args().collect();assert_eq!(args.len(),2);
 let all=Instant::now();let raw=std::fs::read(&args[1]).unwrap();assert!(raw.len()<16*1024*1024);
 let mut r=Cursor::new(raw);let mut magic=[0;8];r.read_exact(&mut magic).unwrap();assert_eq!(&magic,b"NPSHA001");
 let n=u32le(&mut r) as usize;assert!(n>0&&n<100000);let mut messages=vec![];let mut reference=b"NEARSHABATCHV001".to_vec();reference.extend_from_slice(&(n as u64).to_be_bytes());
 let mut compressions=0;let mut total_bytes=0;
 for _ in 0..n{let id=u32le(&mut r);let len=u32le(&mut r) as usize;assert!(len<1<<20);let mut flag=[0];r.read_exact(&mut flag).unwrap();assert!(flag[0]<=1);let mut digest=[0;32];r.read_exact(&mut digest).unwrap();let mut bytes=vec![0;len];r.read_exact(&mut bytes).unwrap();assert_eq!(Sha256::digest(&bytes).as_slice(),&digest);
 let tag=((id as u64)<<32)|((len as u64)<<1)|flag[0] as u64;reference.extend_from_slice(&tag.to_be_bytes());reference.extend_from_slice(&digest);compressions+=(len+9).div_ceil(64);total_bytes+=len;messages.push(Message{id,flag:flag[0],bytes,digest});}
 assert_eq!(r.position() as usize,r.get_ref().len());let expected=Sha512::digest(&reference);
 let start=Instant::now();let b=CircuitBuilder::new();let mut inputs:Vec<Vec<Wire>>=vec![];let mut root_words:Vec<Wire>=reference[..24].chunks_exact(8).map(|x|b.add_constant_64(u64::from_be_bytes(x.try_into().unwrap()))).collect();
 for (i,m) in messages.iter().enumerate(){let wires:Vec<_>=(0..m.bytes.len().div_ceil(4)).map(|_|b.add_witness()).collect();let d=sha256_fixed(&b.subcircuit(format!("message-{i}")),&wires,m.bytes.len());let tag=((m.id as u64)<<32)|((m.bytes.len() as u64)<<1)|m.flag as u64;root_words.push(b.add_constant_64(tag));for j in 0..4{root_words.push(b.bxor(b.shl(d[2*j],32),d[2*j+1]));}inputs.push(wires);}
 let computed=sha512_fixed(&b.subcircuit("batch-root"),&root_words,reference.len());let output:Vec<_>=computed.iter().map(|_|b.add_inout()).collect();for i in 0..8{b.assert_eq(format!("batch-root-{i}"),computed[i],output[i]);}let circuit=b.build();let circuit_s=start.elapsed().as_secs_f64();
 let start=Instant::now();let cs=circuit.constraint_system().clone();let log=Liop::new(cs.clone()).log_witness_elems();let suite=SUITES.iter().find(|s|s.witness_log_len as usize>=log).expect("geometry beyond audited size screen");let params=Params::with_base(log as u32,suite.column_log_len_recursive,suite.moduli[0],suite.moduli[1..].to_vec(),PcsOpening::Recursive).unwrap();let mut session=Session::with_params(cs,params,[0x5A;32]);let setup_s=start.elapsed().as_secs_f64();
 println!("NEAR_BATCH_SETUP {{\"messages\":{n},\"message_bytes\":{total_bytes},\"sha256_compressions\":{compressions},\"sha512_root_compressions\":{},\"witness_log_elems\":{log},\"column_log\":{},\"parameter_suite_ceiling\":\"{}\",\"circuit_s\":{circuit_s},\"setup_s\":{setup_s}}}",(reference.len()+17).div_ceil(128),suite.column_log_len_recursive,suite.name);
 for repeat in 0..3{let start=Instant::now();let mut filler=circuit.new_witness_filler();for(m,ws)in messages.iter().zip(&inputs){for(w,v)in ws.iter().zip(pack32(&m.bytes)){filler[*w]=Word(v);}}for(w,v)in output.iter().zip(expected.chunks_exact(8)){filler[*w]=Word(u64::from_be_bytes(v.try_into().unwrap()));}circuit.populate_wire_witness(&mut filler).expect("reference SHA roots agree");let witness=filler.into_value_vec();let witness_s=start.elapsed().as_secs_f64();let start=Instant::now();let(mut proof,_timing,sizes)=session.prove(&witness,None);let prove_s=start.elapsed().as_secs_f64();let first_ready_s=all.elapsed().as_secs_f64();let start=Instant::now();session.verify(witness.inout(),&proof).expect("honest batch");let verify_s=start.elapsed().as_secs_f64();let mut bad=witness.inout().to_vec();bad[0].0^=1;assert!(session.verify(&bad,&proof).is_err());let pos=proof.tape.len()/2;proof.tape[pos]^=1;assert!(session.verify(witness.inout(),&proof).is_err());proof.tape[pos]^=1;match &mut proof.opening{Opening::Recursive{proof,..}=>proof.norms_mut()[0]+=1,_=>panic!("wrong opening")};assert!(session.verify(witness.inout(),&proof).is_err());
 println!("NEAR_BATCH_RESULT {{\"repeat\":{repeat},\"public_bytes\":{},\"witness_s\":{witness_s},\"prove_s\":{prove_s},\"verify_s\":{verify_s},\"elapsed_since_process_start_before_verification_s\":{first_ready_s},\"analytic_proof_bytes\":{},\"tape_bytes\":{},\"negative_checks\":3}}",witness.inout().len()*8,sizes.total(),proof.tape.len());}
}
