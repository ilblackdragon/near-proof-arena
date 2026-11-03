//! E2E M4c (non-vacuity): dump an honest trace for the Lean checker
//! (`wasm-base-lean/WasmBase/Check/TraceDump.lean`, `wasmbase-tool holds`).
//!
//! Only writes what the prover already built (matrices, public values, the SHA-512 chip's
//! compression inputs); no proving logic is touched.
//!
//! Format: little-endian `u32` words
//!   `0x4454504E` ("NPTD"), version 1,
//!   `npub`, `pub[npub]`,
//!   `ntables`, per table `height`, `width`, `cells[height·width]` (row-major, canonical),
//!   `ncomps`, per compression `cid`, then the 8 + 16 input words `h ‖ block`, each as `lo, hi`.
//! The chip's id of compression `k` is `128·k` (`seg::chip_if`).
use crate::config::F;
use crate::s384::reference::Comp;
use p3_field::PrimeField32;
use p3_matrix::dense::RowMajorMatrix;

pub fn write(path: &str, mats: &[RowMajorMatrix<F>], pubs: &[F], comps: &[Comp]) {
    let mut w: Vec<u32> = vec![0x4454504E, 1, pubs.len() as u32];
    w.extend(pubs.iter().map(|x| x.as_canonical_u32()));
    w.push(mats.len() as u32);
    for m in mats {
        let width = m.width;
        let h = if width == 0 { 0 } else { m.values.len() / width };
        w.push(h as u32);
        w.push(width as u32);
        w.extend(m.values.iter().map(|x| x.as_canonical_u32()));
    }
    w.push(comps.len() as u32);
    for (k, c) in comps.iter().enumerate() {
        w.push((128 * k) as u32);
        for x in c.h.iter().chain(c.block.iter()) {
            w.push(*x as u32);
            w.push((*x >> 32) as u32);
        }
    }
    let bytes: Vec<u8> = w.iter().flat_map(|x| x.to_le_bytes()).collect();
    std::fs::write(path, bytes).unwrap();
    println!("DUMP {path}: {} tables, {} publics, {} compressions, {} bytes", mats.len(), pubs.len(), comps.len(), 4 * w.len());
}
