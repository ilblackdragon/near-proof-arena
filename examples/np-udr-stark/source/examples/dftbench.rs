use std::time::Instant;
use p3_dft::{Radix2DFTSmallBatch, Radix2DitParallel, TwoAdicSubgroupDft};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_monty_31::dft::RecursiveDft;
use npudr::field::F;
use p3_field::PrimeCharacteristicRing;
fn run<D: TwoAdicSubgroupDft<F>>(name: &str, d: D, m: &RowMajorMatrix<F>) {
    let s = F::from_u64(31);
    let _ = d.coset_dft_batch(m.clone(), s).to_row_major_matrix();
    let t = Instant::now();
    for _ in 0..3 { let r = d.coset_dft_batch(m.clone(), s).to_row_major_matrix(); assert!(r.height()>0); }
    println!("{name}: {:.3}s per coset DFT", t.elapsed().as_secs_f64()/3.0);
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let h: usize = a[1].parse().unwrap(); let w: usize = a[2].parse().unwrap();
    let m = RowMajorMatrix::new((0..(w<<h) as u64).map(|i| F::from_u64(i*7+1)).collect(), w);
    run("Radix2DitParallel", Radix2DitParallel::<F>::default(), &m);
    run("SmallBatch", Radix2DFTSmallBatch::<F>::default(), &m);
    run("RecursiveDft", RecursiveDft::<F>::new(1<<h), &m);
}
