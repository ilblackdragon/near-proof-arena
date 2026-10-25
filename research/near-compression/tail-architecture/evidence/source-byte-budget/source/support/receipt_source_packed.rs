//! D0a transfer source serialization from the SAME wires as the outcome kernel.
//! No list membership, account authentication or full runtime claim.
use binius_frontend::{CircuitBuilder,Wire};
use binius_circuits::{fixed_byte_vec::ByteVec};
use crate::{outcome,packed::concat};
pub struct Extra{pub signer_len:Wire,pub signer:[Wire;8],pub key_kind:Wire,pub key:[Wire;8]}
fn fixed(b:&CircuitBuilder,data:Vec<Wire>,len:usize)->ByteVec{ByteVec::new_const_len(b,data,len)}
fn name(b:&CircuitBuilder,len:Wire,data:&[Wire])->ByteVec{
 b.assert_false("name-too-long",b.icmp_ugt(len,b.add_constant_64(64)));
 // NEAR name grammar is a separate execution obligation. Empty signer is
 // allowed here to match serialization, not to claim valid NEAR execution.
 ByteVec::new_with_len_range(data.to_vec(),len,0..=64)
}
pub fn serialize(b:&CircuitBuilder,x:&outcome::Inputs,e:&Extra)->ByteVec{
 b.assert_zero("key-kind-bit",b.shr(e.key_kind,1));
 let key_len=b.select(b.shl(e.key_kind,63),b.add_constant_64(64),b.add_constant_64(32));
 let pre=name(&b.subcircuit("predecessor"),x.predecessor_len,&x.predecessor);
 let recv=name(&b.subcircuit("receiver"),x.receiver_len,&x.receiver);
 let signer=name(&b.subcircuit("signer"),e.signer_len,&e.signer);
 // input_data_ids=[], output_data_receivers=[], actions=[Transfer].
 // For this D0a encoding the exact 13-byte tail is eight zero bytes,
 // u32 action count 1, then u8 Transfer tag 3.
 let fields=vec![fixed(b,vec![x.predecessor_len],4),pre,
 fixed(b,vec![x.receiver_len],4),recv,fixed(b,x.rid.to_vec(),32),
 fixed(b,vec![b.add_constant_64(0)],1),fixed(b,vec![e.signer_len],4),signer,
 fixed(b,vec![e.key_kind],1),ByteVec::new_with_len_range(e.key.to_vec(),key_len,32..=64),
 fixed(b,x.amounts[4].to_vec(),16),fixed(b,vec![b.add_constant_64(0),b.add_constant_64(0x0300000001)],13),
 fixed(b,x.amounts[1].to_vec(),16)];
 concat(b,&fields)
}
pub fn singleton_list(b:&CircuitBuilder,shard:Wire,receipt:ByteVec)->ByteVec{
 concat(b,&[fixed(b,vec![shard,b.add_constant_64(1)],12),receipt])
}
