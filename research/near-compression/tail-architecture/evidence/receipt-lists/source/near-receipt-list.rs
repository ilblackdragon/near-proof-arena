#[path="support/receipt_arithmetic.rs"] mod receipt;
#[path="support/receipt_outcome.rs"] mod outcome;
#[path="support/receipt_source.rs"] mod source;
#[path="support/tight_sha.rs"] mod tight_sha;
#[path="support/receipt_list_wire.rs"] mod wire;
use binius_frontend::CircuitBuilder;
use binius_circuits::{fixed_byte_vec::ByteVec,concat::concat};
use binius_core::word::Word;
use labinius_binius::{Session,Opening,liop::Liop};
use labinius::{Params,Modulus,Opening as PcsOpening,scheme::{SUITES,PublicParameters}};
use std::time::Instant;
fn balanced(b:&CircuitBuilder,mut parts:Vec<ByteVec>)->ByteVec{let mut level=0;while parts.len()>1{parts=parts.chunks(2).enumerate().map(|(i,p)|if p.len()==1{p[0].clone()}else{concat(&b.subcircuit(format!("join-{level}-{i}")),p)}).collect();level+=1;}parts.pop().unwrap()}
fn le(x:&[u8])->u64{u64::from_le_bytes(x.try_into().unwrap())}
fn main(){
 let args:Vec<_>=std::env::args().skip(1).collect();let cap:usize=args[0].parse().unwrap();assert!(cap.is_power_of_two()&&cap<=1024);
 let start=Instant::now();let b=CircuitBuilder::new();let zero=b.add_constant_64(0);let ctx:Vec<_>=(0..5).map(|_|b.add_inout()).collect();b.assert_false("count-cap",b.icmp_ugt(ctx[4],b.add_constant_64(cap as u64)));
 let root:Vec<_>=(0..4).map(|_|b.add_inout()).collect();let mut slots=vec![];let mut parts=vec![];
 for i in 0..cap{
  let sb=b.subcircuit(format!("slot-{i}"));let active=sb.icmp_ult(sb.add_constant_64(i as u64),ctx[4]);let ins:Vec<_>=(0..53).map(|_|sb.add_witness()).collect();
  for(at,j)in [(10,0),(11,1),(34,2)]{sb.assert_eq(format!("context-{j}"),ins[at],sb.select(active,ctx[j],zero));}
  let x=outcome::Inputs{amounts:core::array::from_fn(|j|[ins[2*j],ins[2*j+1]]),predecessor_len:ins[12],predecessor:ins[13..21].try_into().unwrap(),receiver_len:ins[21],receiver:ins[22..30].try_into().unwrap(),rid:ins[30..34].try_into().unwrap(),height:ins[34]};
  let extra=source::Extra{signer_len:ins[35],signer:ins[36..44].try_into().unwrap(),key_kind:ins[44],key:ins[45..53].try_into().unwrap()};
  let bytes=source::serialize(&sb.subcircuit("source"),&x,&extra);let len=sb.select(active,bytes.len_bytes,zero);parts.push(ByteVec::new_with_len_range(bytes.data,len,0..=347));
  let y=outcome::constrain(&sb.subcircuit("outcome"),&x);let out:Vec<_>=(0..11).map(|_|sb.add_inout()).collect();
  let refund=sb.icmp_ne(sb.bor(y.arithmetic.surplus[0],y.arithmetic.surplus[1]),zero);let length=sb.iadd(ins[21],sb.select(refund,sb.add_constant_64(69),sb.add_constant_64(37))).0;
  let values=core::iter::once(sb.add_constant_64(1)).chain(core::iter::once(sb.add_constant_64(i as u64))).chain(core::iter::once(length)).chain(x.rid).chain(y.digest);
  for(j,value)in values.enumerate(){sb.assert_eq(format!("out-{j}"),out[j],sb.select(active,value,zero));}
  slots.push((ins,out));
 }
 let body=balanced(&b.subcircuit("body"),parts);let header=ByteVec::new_const_len(&b,vec![ctx[3],ctx[4]],12);let list=concat(&b.subcircuit("list"),&[header,body]);let digest=tight_sha::sha256_tight(&b.subcircuit("list-hash"),&list,12+347*cap);for i in 0..4{b.assert_eq(format!("root-{i}"),root[i],digest[i]);}
 let c=b.build();let circuit_s=start.elapsed().as_secs_f64();let log=Liop::new(c.constraint_system().clone()).log_witness_elems();println!("RECEIPT_LIST_CIRCUIT cap={cap} log={log} circuit_s={circuit_s}");
 if std::env::var_os("NEAR_GEOMETRY_ONLY").is_some(){return;}
 let suite=SUITES.iter().find(|s|s.witness_log_len as usize>=log).unwrap();let params=Params::with_base(log as u32,suite.column_log_len_recursive,Modulus::Q3889_FS_S,vec![Modulus::Q2917_Q_S,Modulus::Q4861_Q_S,Modulus::Q9721_FS_S,Modulus::Q12637_Q_S],PcsOpening::Recursive).unwrap();let start=Instant::now();let pp=PublicParameters::from_seed(params.clone(),[0x76;32]);let setup=pp.recursion().unwrap();let shape=(setup.key_u.rank(),setup.key_r.rank(),setup.ranks.len());drop(pp);let mut session=Session::with_params(c.constraint_system().clone(),params,[0x76;32]);println!("RECEIPT_LIST_SETUP setup_s={}",start.elapsed().as_secs_f64());
 if let Ok(path)=std::env::var("NEAR_VERIFY_EXPORT"){
  let raw=std::fs::read(path).unwrap();let expected=std::fs::read(std::env::var("NEAR_EXPECTED_PUBLIC").unwrap()).unwrap();assert_eq!(expected.len(),8*(9+11*cap));let start=Instant::now();let(public,mut proof)=unsafe{wire::decode(&raw,&expected,shape)}.unwrap();session.verify(&public,&proof).unwrap();let seconds=start.elapsed().as_secs_f64();let mut wrong=expected.clone();wrong[5*8]^=1;assert!(unsafe{wire::decode(&raw,&wrong,shape)}.is_err());let mut bad=public.clone();bad[5].0^=1;assert!(session.verify(&bad,&proof).is_err());let at=proof.tape.len()/2;proof.tape[at]^=1;assert!(session.verify(&public,&proof).is_err());println!("RECEIPT_LIST_VERIFY bytes={} seconds={seconds} no_witness_loaded=true backend_roundtrip=true negative_checks=3",raw.len());return;
 }
 for path in &args[1..]{let start=Instant::now();let raw=std::fs::read(path).unwrap();assert_eq!(&raw[..8],b"NPLST001");let n=u32::from_le_bytes(raw[40..44].try_into().unwrap()) as usize;assert!(n<=cap);assert_eq!(raw.len(),76+504*n);let context:Vec<_>=raw[8..40].chunks_exact(8).map(le).chain(core::iter::once(n as u64)).collect();let mut w=c.new_witness_filler();for(wire,value)in ctx.iter().zip(&context){w[*wire]=Word(*value);}for(j,wire)in root.iter().enumerate(){w[*wire]=Word(u64::from_be_bytes(raw[44+j*8..52+j*8].try_into().unwrap()));}
  for(i,(ins,out))in slots.iter().enumerate(){let mut data=vec![0u64;53];let mut result=vec![0u64;11];if i<n{let words:Vec<_>=raw[76+i*504..76+(i+1)*504].chunks_exact(8).map(le).collect();data.copy_from_slice(&words[..53]);result[0]=1;result[1]=i as u64;result[2]=data[21]+if words[57]!=0||words[58]!=0{69}else{37};result[3..7].copy_from_slice(&data[30..34]);result[7..11].copy_from_slice(&words[59..63]);}else{data[2]=1;data[12]=1;data[13]=b'p' as u64;data[21]=1;data[22]=b'r' as u64;data[35]=1;data[36]=b's' as u64;}
   for(wire,value)in ins.iter().zip(data){w[*wire]=Word(value);}for(wire,value)in out.iter().zip(result){w[*wire]=Word(value);}
  }
  c.populate_wire_witness(&mut w).unwrap();let w=w.into_value_vec();let prepare_s=start.elapsed().as_secs_f64();let t=Instant::now();let(proof,_,_)=session.prove(&w,None);let prove_s=t.elapsed().as_secs_f64();
  // Full dense diagnostic packet, including fixed-capacity public vector.
  let mut packet=b"NPLIST01".to_vec();let mut part=|x:&[u8]|{packet.extend_from_slice(&(x.len() as u64).to_le_bytes());packet.extend_from_slice(x);};part(&w.inout().iter().flat_map(|w|w.0.to_le_bytes()).collect::<Vec<_>>());part(&proof.tape);part(&labinius::wire::pack_f162(&[proof.claimed_value]));match &proof.opening{Opening::Recursive{left,proof:opening}=>{part(left.t_u().as_bytes());part(opening.t_r().as_bytes());part(&opening.norms().iter().flat_map(|x|x.to_le_bytes()).collect::<Vec<_>>());part(&opening.handle().export_bytes());},_=>panic!()};
  if let Ok(dir)=std::env::var("NEAR_EXPORT_DIR"){std::fs::create_dir_all(&dir).unwrap();std::fs::write(format!("{dir}/{}.packet",std::path::Path::new(path).file_stem().unwrap().to_string_lossy()),&packet).unwrap();}
  let ready_s=start.elapsed().as_secs_f64();let t=Instant::now();session.verify(w.inout(),&proof).unwrap();let verify_s=t.elapsed().as_secs_f64();for at in [0usize,3,4,5,9,12,16]{let mut bad=w.inout().to_vec();bad[at].0^=1;assert!(session.verify(&bad,&proof).is_err());}
  println!("RECEIPT_LIST_RESULT path={path} cap={cap} count={n} bytes={} prepare_s={prepare_s} prove_s={prove_s} ready_s={ready_s} verify_s={verify_s} mutations=7 full_near=false",packet.len());
 }
}
