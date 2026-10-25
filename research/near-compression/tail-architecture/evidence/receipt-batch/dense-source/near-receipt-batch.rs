#[path="support/receipt_arithmetic.rs"] mod receipt;
#[path="support/receipt_outcome_typed.rs"] mod outcome;
#[path="support/tight_sha.rs"] mod tight_sha;
#[path="support/receipt_batch_wire.rs"] mod wire;
use std::{path::Path,time::Instant};
use binius_frontend::{CircuitBuilder,Wire};
use binius_core::word::Word;
use labinius_binius::{Session,Opening,liop::Liop};
use labinius::{Params,Modulus,Opening as PcsOpening,scheme::{SUITES,PublicParameters}};
struct Slot{class:usize,active:Wire,index:Wire,input:Vec<Wire>,output:Vec<Wire>}
struct Record{index:u32,words:Vec<u64>}
fn u64le(x:&[u8])->u64{u64::from_le_bytes(x.try_into().unwrap())}
fn main(){
 let args:Vec<_>=std::env::args().skip(1).collect();assert!(!args.is_empty()||std::env::var_os("NEAR_VERIFY_EXPORT").is_some());
 let start=Instant::now();let b=CircuitBuilder::new();let zero=b.add_constant_64(0);let context:Vec<_>=(0..3).map(|_|b.add_inout()).collect();let mut slots=vec![];
 for(class,&capacity)in wire::CAP.iter().enumerate(){for i in 0..capacity{
  let sb=b.subcircuit(format!("receipt-{class}-{i}"));let active=sb.add_witness();let index=sb.add_witness();sb.assert_zero("active-bit",sb.shr(active,1));sb.assert_zero("index-u32",sb.shr(index,32));let cond=sb.shl(active,63);sb.assert_zero("inactive-index",sb.select(cond,zero,index));
  let input:Vec<_>=(0..35).map(|_|sb.add_witness()).collect();
  // Declared block context is shared by all ACTIVE receipts. Inactive class
  // padding uses a valid fixed dummy context, even if no refund is possible in the real one.
  sb.assert_eq("block-gas-lo",input[10],sb.select(cond,context[0],zero));sb.assert_eq("block-gas-hi",input[11],sb.select(cond,context[1],zero));sb.assert_eq("block-height",input[34],sb.select(cond,context[2],zero));
  let x=outcome::Inputs{amounts:core::array::from_fn(|i|[input[2*i],input[2*i+1]]),predecessor_len:input[12],predecessor:input[13..21].try_into().unwrap(),receiver_len:input[21],receiver:input[22..30].try_into().unwrap(),rid:input[30..34].try_into().unwrap(),height:input[34]};
  let y=outcome::constrain(&sb,&x,outcome::SHAPES[class]);let output:Vec<_>=(0..11).map(|_|sb.add_inout()).collect();sb.assert_eq("public-active",active,output[0]);sb.assert_eq("public-index",index,output[1]);
  let values=core::iter::once(y.length).chain(input[30..34].iter().copied()).chain(y.digest);
  for(j,value)in values.enumerate(){sb.assert_eq(format!("public-{j}"),output[2+j],sb.select(cond,value,zero));}
  slots.push(Slot{class,active,index,input,output});
 }}
 let c=b.build();let circuit_s=start.elapsed().as_secs_f64();let log=Liop::new(c.constraint_system().clone()).log_witness_elems();let suite=SUITES.iter().find(|s|s.witness_log_len as usize>=log).unwrap();
 let params=Params::with_base(log as u32,suite.column_log_len_recursive,Modulus::Q3889_FS_S,vec![Modulus::Q2917_Q_S,Modulus::Q4861_Q_S,Modulus::Q9721_FS_S,Modulus::Q12637_Q_S],PcsOpening::Recursive).unwrap();let seed=[0x73;32];
 let start=Instant::now();let pp=PublicParameters::from_seed(params.clone(),seed);let setup=pp.recursion().unwrap();let shape=(setup.key_u.rank(),setup.key_r.rank(),setup.ranks.len());let binary_rank=setup.ranks[1];drop(pp);
 let mut session=Session::with_params(c.constraint_system().clone(),params,seed);let setup_s=start.elapsed().as_secs_f64();
 println!("RECEIPT_BATCH_SETUP log={log} public_bytes={} left_rank={} opening_rank={} norms={} binary_rank={binary_rank} circuit_s={circuit_s} setup_s={setup_s}",wire::PUBLIC_BYTES,shape.0,shape.1,shape.2);
 if let Ok(path)=std::env::var("NEAR_VERIFY_EXPORT"){
  let raw=std::fs::read(path).unwrap();let ctx=std::fs::read(std::env::var("NEAR_EXPECTED_CONTEXT").unwrap()).unwrap();let root=std::fs::read(std::env::var("NEAR_OUTCOME_ROOT").unwrap()).unwrap();let start=Instant::now();
  let(public,mut proof)=unsafe{wire::decode(&raw,&ctx,&root,shape)}.unwrap();let decode_s=start.elapsed().as_secs_f64();let start=Instant::now();session.verify(&public,&proof).unwrap();let verify_s=start.elapsed().as_secs_f64();
  let mut bad=public.clone();bad[0].0^=1;assert!(session.verify(&bad,&proof).is_err());let at=proof.tape.len()/2;proof.tape[at]^=1;assert!(session.verify(&public,&proof).is_err());
  println!("RECEIPT_BATCH_VERIFY bytes={} decode_s={decode_s} verify_s={verify_s} no_witness_loaded=true backend_roundtrip=true wrong_context_tape_rejected=true full_near=false",raw.len());return;
 }
 for path in args{
  let start=Instant::now();let raw=std::fs::read(&path).unwrap();assert_eq!(&raw[..8],b"NPRCB001");let ctx=&raw[8..32];let count=u32::from_le_bytes(raw[32..36].try_into().unwrap()) as usize;assert_eq!(raw.len(),36+364*count);let mut classes:Vec<Vec<Record>>=(0..4).map(|_|vec![]).collect();
  for row in raw[36..].chunks_exact(364){let index=u32::from_le_bytes(row[..4].try_into().unwrap());let words:Vec<_>=row[4..].chunks_exact(8).map(u64le).collect();assert_eq!(words[10],u64le(&ctx[..8]));assert_eq!(words[11],u64le(&ctx[8..16]));assert_eq!(words[34],u64le(&ctx[16..]));let refund=words[39]!=0||words[40]!=0;let class=if refund{if words[21]<=50{2}else{3}}else{if words[21]<=18{0}else{1}};classes[class].push(Record{index,words});}
  for(i,rows)in classes.iter_mut().enumerate(){rows.sort_by_key(|r|r.index);assert!(rows.len()<=wire::CAP[i]);}
  let mut w=c.new_witness_filler();let mut public=ctx.to_vec();for(i,x)in context.iter().enumerate(){w[*x]=Word(u64le(&ctx[8*i..8*i+8]));}let mut cursor=[0;4];
  for slot in &slots{
   let shape=outcome::SHAPES[slot.class];let mut data=vec![0u64;35];let mut out=vec![0u64;11];
   if let Some(r)=classes[slot.class].get(cursor[slot.class]){data.copy_from_slice(&r.words[..35]);out[0]=1;out[1]=r.index as u64;out[2]=data[21]+if shape.refund{69}else{37};out[3..7].copy_from_slice(&data[30..34]);out[7..11].copy_from_slice(&r.words[41..45]);}
   else{data[2]=1;data[8]=if shape.refund{1}else{0};data[12]=4;data[13]=u64::from_le_bytes(*b"user\0\0\0\0");data[21]=shape.min_receiver as u64;for v in &mut data[22..30]{*v=u64::from_le_bytes(*b"aaaaaaaa");}}
   cursor[slot.class]+=1;w[slot.active]=Word(out[0]);w[slot.index]=Word(out[1]);for(x,v)in slot.input.iter().zip(data){w[*x]=Word(v);}for(x,v)in slot.output.iter().zip(out){w[*x]=Word(v);public.extend_from_slice(&v.to_le_bytes());}
  }
  assert_eq!(public.len(),wire::PUBLIC_BYTES);let root=std::fs::read(Path::new(&path).with_extension("root")).unwrap();assert_eq!(wire::outcome_root(&public,ctx).unwrap().as_slice(),root);c.populate_wire_witness(&mut w).unwrap();let w=w.into_value_vec();let prepare_s=start.elapsed().as_secs_f64();let prove_start=Instant::now();let(mut proof,_,_)=session.prove(&w,None);let prove_s=prove_start.elapsed().as_secs_f64();
  let mut packet=b"NPRCBP01".to_vec();let mut part=|x:&[u8]|{packet.extend_from_slice(&(x.len() as u64).to_le_bytes());packet.extend_from_slice(x);};part(&public);part(&proof.tape);part(&labinius::wire::pack_f162(&[proof.claimed_value]));
  match &proof.opening{Opening::Recursive{left,proof:opening}=>{part(left.t_u().as_bytes());part(opening.t_r().as_bytes());part(&opening.norms().iter().flat_map(|x|x.to_le_bytes()).collect::<Vec<_>>());part(&opening.handle().export_bytes());},_=>panic!("recursive opening required")};
  let dir=std::env::var("NEAR_EXPORT_DIR").unwrap();std::fs::create_dir_all(&dir).unwrap();let name=Path::new(&path).file_stem().unwrap().to_string_lossy();std::fs::write(format!("{dir}/{name}.packet"),&packet).unwrap();let ready_s=start.elapsed().as_secs_f64();let verify_start=Instant::now();session.verify(w.inout(),&proof).unwrap();let verify_s=verify_start.elapsed().as_secs_f64();
  for i in [0usize,3,4,5,6,10]{let mut bad=w.inout().to_vec();bad[i].0^=1;assert!(session.verify(&bad,&proof).is_err());}let at=proof.tape.len()/2;proof.tape[at]^=1;assert!(session.verify(w.inout(),&proof).is_err());
  println!("RECEIPT_BATCH_RESULT case={name} receipts={count} packet_bytes={} prepare_s={prepare_s} prove_s={prove_s} ready_s={ready_s} verify_s={verify_s} negative_checks=7",packet.len());
 }
}
