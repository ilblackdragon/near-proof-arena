//! Exact reference-transform parity and a replay of the measured 2^20 x 102 DFT shape.
use openvm_recursion_circuit::sha384::config::F;
use openvm_stark_backend::prover::fast_dft::coset_dft_rows_multi_into;
use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
use p3_field::{Field, PackedValue, PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::{hint::black_box, time::Instant};

fn input(log: usize, width: usize) -> Vec<F> {
    (0..(1 << log) * width)
        .map(|i| F::from_u32(((i as u64 * 1234567 + 2013265919) % 2013265921) as u32))
        .collect()
}
fn main() {
    let bench = std::env::args().nth(1).as_deref() == Some("bench");
    println!("DFT_PACKING_WIDTH {}", <F as Field>::Packing::WIDTH);
    if bench {
        let coeffs = input(20, 102);
        let (mut scratch, mut out) = (vec![], vec![]);
        let mut times = vec![];
        for i in 0..18 {
            let t = Instant::now();
            coset_dft_rows_multi_into(&coeffs, 102, &[F::from_u32(7 + i)], &mut scratch, &mut out);
            let seconds = t.elapsed().as_secs_f64();
            black_box(&out);
            if i >= 2 {
                times.push(seconds);
            }
        }
        times.sort_by(f64::total_cmp);
        println!(
            "DFT_BENCH log=20 width=102 repeats={} median_s={:.6} mean_s={:.6} checksum={}",
            times.len(),
            (times[7] + times[8]) / 2.0,
            times.iter().sum::<f64>() / times.len() as f64,
            out[out.len() / 2].as_canonical_u32()
        );
        return;
    }
    let mut checked = 0;
    for (log, width, groups) in [
        (8, 3, 1),
        (12, 1, 1),
        (12, 3, 2),
        (12, 12, 4),
        (12, 76, 1),
        (12, 83, 1),
        (16, 102, 1),
        (20, 102, 1),
    ] {
        let coeffs = input(log, width);
        let (mut scratch, mut out) = (vec![], vec![]);
        for repeat in 0..2 {
            let shifts: Vec<_> = (0..groups)
                .map(|k| F::from_u32(7 + k as u32 + repeat))
                .collect();
            coset_dft_rows_multi_into(&coeffs, width, &shifts, &mut scratch, &mut out);
            assert_eq!(out.len(), coeffs.len() * groups);
            for (k, &shift) in shifts.iter().enumerate() {
                let reference = Radix2Dit::<F>::default()
                    .coset_dft_batch(RowMajorMatrix::new(coeffs.clone(), width), shift)
                    .values;
                for (row, expected) in reference.chunks_exact(width).enumerate() {
                    assert_eq!(
                        &out[row * groups * width + k * width
                            ..row * groups * width + (k + 1) * width],
                        expected,
                        "log={log} width={width} group={k} row={row} repeat={repeat}"
                    );
                }
            }
            checked += 1;
        }
        println!("DFT_REFERENCE_OK log={log} width={width} groups={groups} reused_buffers=true");
    }
    println!("DFT_PARITY_OK cases={checked}");
}
