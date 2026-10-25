//! Diagnostic metadata of the measured fixed template; no proving/security claim.
use labinius::{Params,Opening,Modulus,scheme::{SUITES,PublicParameters}};
fn main(){
 let suite=&SUITES[2];let mut primes=suite.moduli.to_vec();
 for count in 3..=5 {
 if count==4 {primes.push(Modulus::Q9721_FS_S);}
 if count==5 {primes.push(Modulus::Q12637_Q_S);}
 let params=Params::with_base(22,10,primes[0],primes[1..].to_vec(),Opening::Recursive).unwrap();
 let pp=PublicParameters::from_seed(params.clone(),[0x69;32]);
 let setup=pp.recursion().unwrap();
 for (label,group,key) in [("Y",setup.residues.clone(),&setup.key_y),("u",vec![setup.left_expansion],&setup.key_u),("R",setup.rest.clone(),&setup.key_r)] {
  let columns:usize=group.iter().map(|&i|setup.ranks[i]).sum();
  let normsq:u64=group.iter().map(|&i|setup.caps[i]).sum();
  println!("{{\"modulus_count\":{count},\"role\":\"{label}\",\"rank\":{},\"columns\":{columns},\"normsq_cap\":{normsq},\"group\":{group:?}}}",key.rank());
 }
 println!("SHAPE count={count} n={} r={} caps={:?} ranks={:?} binary={:?}",setup.n,setup.r,setup.caps,setup.ranks,setup.binary);
 }
}
