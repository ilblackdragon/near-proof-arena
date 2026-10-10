use npudr::field::F;
use p3_dft::{Radix2DFTSmallBatch, Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use std::time::Instant;
fn run<D: TwoAdicSubgroupDft<F>>(name: &str, d: &D, h: usize, w: usize) {
    let m = RowMajorMatrix::new(
        (0..(w << h) as u64)
            .map(|i| F::from_u64(i * 7 + 1))
            .collect(),
        w,
    );
    let _ = d.idft_batch(m.clone());
    let t = Instant::now();
    for _ in 0..3 {
        let c = d.idft_batch(m.clone());
        assert!(c.height() > 0);
    }
    let per = t.elapsed().as_secs_f64() / 3.0;
    println!(
        "{name} 2^{h} x {w}: {:.3}s  ({:.1} ms/col)",
        per,
        per * 1000.0 / w as f64
    );
}
fn main() {
    let h = 22;
    let a = Radix2DitParallel::<F>::default();
    let b = Radix2DFTSmallBatch::<F>::default();
    for w in [8usize, 16, 32, 64, 128] {
        run("DitPar", &a, h, w);
        run("SmallB", &b, h, w);
    }
}
