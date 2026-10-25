#[path="support/local_wire.rs"] mod local_wire;
#[path="support/tight_sha.rs"] mod tight_sha;
use std::{io::{Cursor,Read},time::Instant};
use sha2::{Digest,Sha256,Sha512};
use binius_core::word::Word;
use binius_frontend::{CircuitBuilder,Wire};
use binius_circuits::{fixed_byte_vec::ByteVec,sha512::sha512_fixed};
use labinius_binius::{Session,Opening,liop::Liop};
use labinius::{Params,Opening as PcsOpening,scheme::SUITES};
use labinius_bench::pin;
const POLICY:&[(usize,usize)]=&[(1,1024),(2,2048),(4,8),(8,4),(16,2),(32,1),(2048,1)];
struct Message{id:u32,flag:u8,bytes:Vec<u8>}
struct Slot{active:Wire,id:Wire,flag:Wire,message:ByteVec}
fn u32le(r:&mut Cursor<Vec<u8>>)->u32{let mut b=[0;4];r.read_exact(&mut b).unwrap();u32::from_le_bytes(b)}
fn read_batch(path:&str)->Vec<Message>{
 let raw=std::fs::read(path).unwrap();assert!(raw.len()<16*1024*1024);let mut r=Cursor::new(raw);let mut magic=[0;8];r.read_exact(&mut magic).unwrap();assert_eq!(&magic,b"NPSHA001");let n=u32le(&mut r);assert!(n<100000);let mut out=vec![];
 for _ in 0..n{let id=u32le(&mut r);let len=u32le(&mut r) as usize;assert!(len<1<<20);let mut flag=[0];r.read_exact(&mut flag).unwrap();assert!(flag[0]<=1);let mut digest=[0;32];r.read_exact(&mut digest).unwrap();let mut bytes=vec![0;len];r.read_exact(&mut bytes).unwrap();assert_eq!(Sha256::digest(&bytes).as_slice(),&digest);out.push(Message{id,flag:flag[0],bytes});}
 assert_eq!(r.position() as usize,r.get_ref().len());out
}
fn main(){
 pin(8);let args:Vec<_>=std::env::args().skip(1).collect();assert!(args.len()>=2 || std::env::var_os("NEAR_VERIFY_EXPORT").is_some(),"pass batches or local verify mode");
 let start=Instant::now();let b=CircuitBuilder::new();let zero=b.add_constant_64(0);let n:usize=POLICY.iter().map(|p|p.1).sum();
 let mut header=b"NEARSHATEMPL0001".to_vec();header.extend_from_slice(&(n as u64).to_be_bytes());
 let mut root:Vec<Wire>=header.chunks_exact(8).map(|x|b.add_constant_64(u64::from_be_bytes(x.try_into().unwrap()))).collect();
 let mut slots=vec![];
 for &(blocks,count) in POLICY{for slot in 0..count{
  let sb=b.subcircuit(format!("bucket-{blocks}-slot-{slot}"));let active=sb.add_witness();let id=sb.add_witness();let flag=sb.add_witness();let len=sb.add_witness();
  sb.assert_false("active-bit",sb.shr(active,1));sb.assert_false("flag-bit",sb.shr(flag,1));sb.assert_false("id-u32",sb.shr(id,32));
  let cond=sb.shl(active,63);
  for (name,w) in [("inactive-id",id),("inactive-flag",flag),("inactive-length",len)]{sb.assert_false(name,sb.select(cond,zero,w));}
  let max_len=64*blocks-9;sb.assert_false("bucket-length",sb.icmp_ugt(len,sb.add_constant_64(max_len as u64)));
  let message=ByteVec::new((0..max_len.div_ceil(8)).map(|_|sb.add_witness()).collect(),len);
  let digest=tight_sha::sha256_tight(&sb,&message,max_len);
  let tag=sb.bxor(sb.shl(id,32),sb.bxor(sb.shl(len,1),flag));root.push(active);root.push(tag);root.extend_from_slice(&digest);
  slots.push(Slot{active,id,flag,message});
 }}
 let root_bytes=root.len()*8;let computed=sha512_fixed(&b.subcircuit("root"),&root,root_bytes);let outputs:Vec<_>=(0..8).map(|_|b.add_inout()).collect();for i in 0..8{b.assert_eq(format!("root-{i}"),computed[i],outputs[i]);}let circuit=b.build();let circuit_s=start.elapsed().as_secs_f64();
 let start=Instant::now();let cs=circuit.constraint_system().clone();let log=Liop::new(cs.clone()).log_witness_elems();let suite=SUITES.iter().find(|s|s.witness_log_len as usize>=log).expect("unsupported geometry");let params=Params::with_base(log as u32,suite.column_log_len_recursive,suite.moduli[0],suite.moduli[1..].to_vec(),PcsOpening::Recursive).unwrap();let mut session=Session::with_params(cs,params,[0x69;32]);let setup_s=start.elapsed().as_secs_f64();
 println!("TEMPLATE_SETUP {{\"message_slots\":{n},\"nominal_blocks\":7296,\"constructed_sha_blocks\":7296,\"root_bytes\":{root_bytes},\"witness_log_elems\":{log},\"circuit_s\":{circuit_s},\"setup_s\":{setup_s}}}");
 if let Ok(path)=std::env::var("NEAR_VERIFY_EXPORT") {
  let expected=std::fs::read(std::env::var("NEAR_EXPECTED_ROOT").expect("independent root path")).unwrap();
  let raw=std::fs::read(&path).unwrap();let start=Instant::now();
  // SAFETY: this command is a local research harness consuming our own exports;
  // do not expose it as an untrusted service.
  let (public,mut proof)=unsafe{local_wire::decode(&raw,&expected)}.expect("decode local export");let decode_s=start.elapsed().as_secs_f64();
  let start=Instant::now();session.verify(&public,&proof).expect("decoded proof verifies");let verify_s=start.elapsed().as_secs_f64();
  let mut wrong=public.clone();wrong[0].0^=1;assert!(session.verify(&wrong,&proof).is_err());
  let at=proof.tape.len()/2;proof.tape[at]^=1;assert!(session.verify(&public,&proof).is_err());
  println!("LOCAL_WIRE_VERIFY bytes={} decode_s={decode_s} verify_s={verify_s} backend_byte_roundtrip=true wrong_root_rejected=true wrong_tape_rejected=true no_witness_loaded=true",raw.len());return;
 }
 for path in &args{
  let batch_start=Instant::now();let messages=read_batch(path);let mut buckets:Vec<Vec<&Message>>=POLICY.iter().map(|_|vec![]).collect();for m in &messages{let blocks=(m.bytes.len()+9).div_ceil(64);let idx=POLICY.iter().position(|p|blocks<=p.0).expect("message too long");buckets[idx].push(m);}
  let mut ordered=vec![];for (i,&(_,capacity)) in POLICY.iter().enumerate(){buckets[i].sort_by_key(|m|m.id);assert!(buckets[i].len()<=capacity,"bucket overflow");for j in 0..capacity{ordered.push(buckets[i].get(j).copied());}}
  let mut expected_bytes=header.clone();let mut filler=circuit.new_witness_filler();
  for (s,m) in slots.iter().zip(&ordered){let (active,id,flag,data)=match m{Some(m)=>(1u64,m.id,m.flag,m.bytes.as_slice()),None=>(0,0,0,&[][..])};filler[s.active]=Word(active);filler[s.id]=Word(id as u64);filler[s.flag]=Word(flag as u64);filler[s.message.len_bytes]=Word(data.len() as u64);for (i,w) in s.message.data.iter().enumerate(){let mut word=[0;8];let begin=i*8;if begin<data.len(){let end=(begin+8).min(data.len());word[..end-begin].copy_from_slice(&data[begin..end]);}filler[*w]=Word(u64::from_le_bytes(word));}
   expected_bytes.extend_from_slice(&active.to_be_bytes());let tag=((id as u64)<<32)|((data.len() as u64)<<1)|flag as u64;expected_bytes.extend_from_slice(&tag.to_be_bytes());expected_bytes.extend_from_slice(&Sha256::digest(data));
  }
  assert_eq!(expected_bytes.len(),root_bytes);let expected=Sha512::digest(&expected_bytes);for (w,v) in outputs.iter().zip(expected.chunks_exact(8)){filler[*w]=Word(u64::from_be_bytes(v.try_into().unwrap()));}
  circuit.populate_wire_witness(&mut filler).expect("independent host hash root matches");let witness=filler.into_value_vec();let prepare_s=batch_start.elapsed().as_secs_f64();let start=Instant::now();let(mut proof,_,sizes)=session.prove(&witness,None);let prove_s=start.elapsed().as_secs_f64();let export_start=Instant::now();
  if let Ok(dir)=std::env::var("NEAR_EXPORT_DIR") {
   let mut packet=b"NPTMPL01".to_vec();
   let mut part=|bytes:&[u8]| {packet.extend_from_slice(&(bytes.len() as u64).to_le_bytes());packet.extend_from_slice(bytes);};
   part(&expected);part(&proof.tape);part(&labinius::wire::pack_f162(&[proof.claimed_value]));
   match &proof.opening {Opening::Recursive{left,proof:opening}=>{
    part(left.t_u().as_bytes());part(opening.t_r().as_bytes());
    let norms:Vec<u8>=opening.norms().iter().flat_map(|n|n.to_le_bytes()).collect();part(&norms);
    let backend=opening.handle().export_bytes();part(&backend);
    std::fs::create_dir_all(&dir).unwrap();let case=std::path::Path::new(path).parent().unwrap().file_name().unwrap().to_string_lossy();
    std::fs::write(format!("{dir}/{case}.backend"),&backend).unwrap();
    std::fs::write(format!("{dir}/{case}.packet"),&packet).unwrap();
    println!("EXPORT_BYTES case={case} backend={} total={} analytical={} codec=export_only_rns",backend.len(),packet.len(),sizes.total());
   },_=>panic!("recursive required")};
  }
  let export_s=export_start.elapsed().as_secs_f64();let ready_s=batch_start.elapsed().as_secs_f64();let start=Instant::now();session.verify(witness.inout(),&proof).expect("honest template proof");let verify_s=start.elapsed().as_secs_f64();
  println!("EXPORT_TIME seconds={export_s} included_in_ready=true");
  for (offset,bit) in [(24usize,1u8),(32,1),(39,2),(40,1)]{let mut changed=expected_bytes.clone();changed[offset]^=bit;let digest=Sha512::digest(&changed);let bad:Vec<_>=digest.chunks_exact(8).map(|v|Word(u64::from_be_bytes(v.try_into().unwrap()))).collect();assert!(session.verify(&bad,&proof).is_err());}let pos=proof.tape.len()/2;proof.tape[pos]^=1;assert!(session.verify(witness.inout(),&proof).is_err());proof.tape[pos]^=1;match &mut proof.opening{Opening::Recursive{proof,..}=>proof.norms_mut()[0]+=1,_=>panic!("not recursive")};assert!(session.verify(witness.inout(),&proof).is_err());
  println!("TEMPLATE_RESULT {{\"path\":\"{path}\",\"messages\":{},\"prepare_s\":{prepare_s},\"prove_s\":{prove_s},\"ready_s\":{ready_s},\"verify_s\":{verify_s},\"analytic_proof_bytes\":{},\"public_bytes\":64,\"negative_checks\":6}}",messages.len(),sizes.total());
 }
}
