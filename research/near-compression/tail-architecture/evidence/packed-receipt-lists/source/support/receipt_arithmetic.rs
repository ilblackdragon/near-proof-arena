//! D0a transfer arithmetic only. Inputs still need authenticated receipt/state binding.
use binius_frontend::{CircuitBuilder,Wire};
pub type U128=[Wire;2]; // little-endian limbs
pub struct Inputs{pub before:U128,pub deposit:U128,pub locked:U128,pub storage:U128,pub gas_price:U128,pub block_gas_price:U128,pub system:Wire}
pub struct Outputs{pub after:U128,pub burnt:U128,pub surplus:U128}
fn constant(b:&CircuitBuilder,x:u128)->U128{[b.add_constant_64(x as u64),b.add_constant_64((x>>64) as u64)]}
fn select(b:&CircuitBuilder,c:Wire,t:U128,f:U128)->U128{[b.select(c,t[0],f[0]),b.select(c,t[1],f[1])]}
fn lt(b:&CircuitBuilder,a:U128,c:U128)->Wire{b.select(b.icmp_eq(a[1],c[1]),b.icmp_ult(a[0],c[0]),b.icmp_ult(a[1],c[1]))}
fn add(b:&CircuitBuilder,a:U128,c:U128)->U128{let(lo,carry)=b.iadd(a[0],c[0]);let(hi,overflow)=b.iadd_cin_cout(a[1],c[1],carry);b.assert_false("addition-overflow",overflow);[lo,hi]}
fn sub(b:&CircuitBuilder,a:U128,c:U128)->U128{let zero=b.add_constant_64(0);let(lo,borrow)=b.isub_bin_bout(a[0],c[0],zero);let(hi,overflow)=b.isub_bin_bout(a[1],c[1],borrow);b.assert_false("subtraction-underflow",overflow);[lo,hi]}
fn mul_constant(b:&CircuitBuilder,a:U128,c:u64)->U128{
 // The current LaBinius LIOP has no IntMul oracle. Constant shift/add stays
 // in its supported AND/shift relations. Positive partial sums cannot hide overflow.
 let mut out=constant(b,0);
 for k in 0..64u32 {if (c>>k)&1==0{continue;}
  let shifted=if k==0{a}else{
   b.assert_zero(format!("shift-overflow-{k}"),b.shr(a[1],64-k));
   [b.shl(a[0],k),b.bor(b.shl(a[1],k),b.shr(a[0],64-k))]
  };
  out=add(&b.subcircuit(format!("sum-{k}")),out,shifted);
 }out
}
pub fn constrain(b:&CircuitBuilder,x:&Inputs)->Outputs{
 b.assert_zero("system-bit",b.shr(x.system,1));let sys=b.shl(x.system,63);let zero=constant(b,0);
 let after=add(&b.subcircuit("credit"),x.before,x.deposit);
 // Native credited() excludes exactly u128::MAX as well as arithmetic overflow.
 b.assert_true("credited-below-max",lt(b,after,constant(b,u128::MAX)));
 let total=add(&b.subcircuit("balance-plus-locked"),after,x.locked);
 let need=mul_constant(&b.subcircuit("storage-price"),x.storage,10_000_000_000_000_000_000);
 // Either storage <= 770 or total >= storage cost. Conditions are MSB booleans.
 let low_storage=lt(b,x.storage,constant(b,771));let covered=b.bnot(lt(b,total,need));
 b.assert_true("storage-covered",b.bor(low_storage,covered));
 let effective=select(b,lt(b,x.gas_price,x.block_gas_price),x.gas_price,x.block_gas_price);
 let delta=sub(&b.subcircuit("gas-surplus-price"),x.gas_price,effective);
 // System receipts bypass gas multiplication, including otherwise-overflowing prices.
 let burnt=mul_constant(&b.subcircuit("burnt"),select(b,sys,zero,effective),223_182_562_500);
 let surplus=mul_constant(&b.subcircuit("surplus"),select(b,sys,zero,delta),223_182_562_500);
 Outputs{after,burnt,surplus}
}
