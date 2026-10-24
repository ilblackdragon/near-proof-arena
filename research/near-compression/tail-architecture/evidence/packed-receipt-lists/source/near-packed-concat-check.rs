#[path="support/packed_concat.rs"] mod packed;
use binius_frontend::CircuitBuilder;
use binius_circuits::fixed_byte_vec::ByteVec;
use binius_core::word::Word;
fn main(){let b=CircuitBuilder::new();let ins:Vec<_>=(0..8).map(|_|b.add_inout()).collect();let a=ByteVec::new(ins[2..5].to_vec(),ins[0]);let c=ByteVec::new(ins[5..8].to_vec(),ins[1]);let out=packed::concat(&b,&[a,c]);let expected:Vec<_>=(0..7).map(|_|b.add_inout()).collect();b.assert_eq("length",out.len_bytes,expected[0]);for i in 0..6{b.assert_eq(format!("word-{i}"),out.data[i],expected[1+i]);}let circuit=b.build();let mut checked=0;let mut mutants=0;
 for a in 0..=24{for c in 0..=24{let left:Vec<u8>=(0..24).map(|i|i*3+1).collect();let right:Vec<u8>=(0..24).map(|i|255-i*5).collect();let mut result=left[..a].to_vec();result.extend_from_slice(&right[..c]);result.resize(48,0);let words:Vec<u64>=vec![a as u64,c as u64].into_iter().chain(left.chunks_exact(8).chain(right.chunks_exact(8)).map(|x|u64::from_le_bytes(x.try_into().unwrap()))).chain(core::iter::once((a+c) as u64)).chain(result.chunks_exact(8).map(|x|u64::from_le_bytes(x.try_into().unwrap()))).collect();
 for change in core::iter::once(None).chain((8..15).map(Some)){let mut w=circuit.new_witness_filler();for(i,wire)in ins.iter().chain(expected.iter()).enumerate(){w[*wire]=Word(words[i]^u64::from(change==Some(i)));}let valid=circuit.populate_wire_witness(&mut w).is_ok();assert_eq!(valid,change.is_none(),"lengths {a}/{c}, mutation {change:?}");if change.is_none(){checked+=1}else{mutants+=1}}
 }}
 for invalid in [25u64,1<<32,1<<63]{let mut w=circuit.new_witness_filler();for wire in ins.iter().chain(expected.iter()){w[*wire]=Word(0);}w[ins[0]]=Word(invalid);assert!(circuit.populate_wire_witness(&mut w).is_err());mutants+=1;}
 println!("PACKED_CONCAT cases={checked} rejected_mutations={mutants} dirty_suffixes=true");}
