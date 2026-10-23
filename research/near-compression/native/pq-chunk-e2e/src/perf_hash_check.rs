//! Differential checks of borrowed-row leaf hashing against the unchanged flat path.
use openvm_recursion_circuit::sha384::config::{F, ShaHasher};
use openvm_stark_backend::hasher::MerkleHasher;
use p3_field::PrimeCharacteristicRing;

fn main() {
    // Separate processes can test each supported framing/implementation switch.
    let mut checked = 0;
    for final_layer in [false, true] {
        let hasher = ShaHasher { final_layer };
        for width in [1, 3, 12, 76, 83] {
            for rows in [1, 2, 16] {
                for n in [0, 1, 15, 16, 17, 64] {
                    // A padded, row-interleaved layout exercises the actual stream gather.
                    let stride = width + 3;
                    let matrix: Vec<F> = (0..n * rows * stride)
                        .map(|i| {
                            F::from_u32(((i as u64 * 1234567 + 2013265919) % 2013265921) as u32)
                        })
                        .collect();
                    let get = |leaf: usize, row: usize| {
                        let start = (row * n + leaf) * stride;
                        &matrix[start..start + width]
                    };
                    let mut flat = Vec::new();
                    for leaf in 0..n {
                        for row in 0..rows {
                            flat.extend_from_slice(get(leaf, row));
                        }
                    }
                    assert_eq!(
                        hasher.hash_leaves_flat(&flat, width, rows),
                        hasher.hash_leaves_rows(n, width, rows, get),
                        "final={final_layer} width={width} rows={rows} n={n}"
                    );
                    checked += 1;
                }
            }
        }
    }
    println!("LEAF_PARITY_OK cases={checked}");
}
