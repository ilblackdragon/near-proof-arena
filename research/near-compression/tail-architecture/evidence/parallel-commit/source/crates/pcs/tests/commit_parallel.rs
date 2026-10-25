use labinius::{key::{CommitmentKey,AuxData},ring::Modulus,F162};
use labinius::f162::RandomF162;
use labinius::rng::Rng;
#[test]
fn parallel_matches_serial_matrix_raw_and_retained_transform(){
 let limbs=[Modulus::Q2917_Q_S,Modulus::Q4861_Q_S,Modulus::Q9721_FS_S,Modulus::Q12637_Q_S];
 let mut cases=0;
 for len in [128usize,512]{let key=CommitmentKey::random(len,0x781234,Modulus::Q3889_FS_S,&limbs);
  for r in [1usize,2,4,8,16,32,64]{let mut rng=Rng::new((len+r) as u64);let mut serial=AuxData::new(key.len_ring(),r,key.limbs());let mut parallel=AuxData::new(key.len_ring(),r,key.limbs());
   for pattern in 0..3{let input:Vec<_>=(0..len*r).map(|_|match pattern{0=>F162([0;3]),1=>F162([u64::MAX,u64::MAX,(1u64<<34)-1]),_=>F162::random(&mut rng)}).collect();let expected=key.commit_into_aux(&input,r,&mut serial);
    for workers in [1usize,2,3,4,8]{let actual=key.commit_into_aux_parallel(&input,r,&mut parallel,workers);assert_eq!(actual,expected,"matrix len={len} r={r} workers={workers}");
     for k in 0..key.limbs(){for j in 0..r{assert_eq!(parallel.commitment(k,j),serial.commitment(k,j));}}
     for j in 0..r*serial.batches_per_chunk(){assert_eq!(parallel.batch(j).v,serial.batch(j).v);assert_eq!(parallel.batch(j).representation,serial.batch(j).representation);}
     cases+=1;
    }
   }
  }
 }
 println!("COMMIT_PARITY cases={cases} matrix_raw_retained_transform_exact=true workspace_reused=true");
}
