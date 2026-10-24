use binius_frontend::CircuitBuilder;
use binius_core::word::Word;
fn accepts(strict:bool,active:u64,id:u64,flag:u64,len:u64,public_active:u64,public_tag:u64)->bool{
 let b=CircuitBuilder::new();let a=b.add_witness();let i=b.add_witness();let f=b.add_witness();let l=b.add_witness();let zero=b.add_constant_64(0);
 let guard=|name:&str,w|if strict{b.assert_zero(name,w)}else{b.assert_false(name,w)};
 guard("active-bit",b.shr(a,1));guard("flag-bit",b.shr(f,1));guard("id-u32",b.shr(i,32));
 for (name,w) in [("inactive-id",i),("inactive-flag",f),("inactive-length",l)]{guard(name,b.select(b.shl(a,63),zero,w));}
 b.assert_false("bucket-length",b.icmp_ugt(l,b.add_constant_64(55)));
 b.assert_eq("public-active",a,b.add_constant_64(public_active));
 b.assert_eq("public-tag",b.bxor(b.shl(i,32),b.bxor(b.shl(l,1),f)),b.add_constant_64(public_tag));
 let c=b.build();let mut w=c.new_witness_filler();w[a]=Word(active);w[i]=Word(id);w[f]=Word(flag);w[l]=Word(len);c.populate_wire_witness(&mut w).is_ok()
}
fn main(){
 // Public claims len=10, flag=1, id=3; private hash input can instead have len=11.
 let attacks=[(1,3,3,11,1,(3<<32)|21),(1,3+(1u64<<32),1,10,1,(3<<32)|21),
              (0,0,2,1,0,0),(2,0,0,0,2,0)];
 for &(a,i,f,l,pa,pt) in &attacks{assert!(accepts(false,a,i,f,l,pa,pt));assert!(!accepts(true,a,i,f,l,pa,pt));}
 for strict in [false,true]{assert!(accepts(strict,1,3,1,10,1,(3<<32)|21));assert!(accepts(strict,0,0,0,0,0,0));}
 println!("METADATA_GUARDS legacy_accepts_invalid=4 strict_rejects_invalid=4 honest_passes=4 length_flag_alias_reproduced=true");
}
