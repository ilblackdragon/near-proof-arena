//! Decoder + executor robustness on arbitrary bytes: never panics, and the
//! fuel accounting is consistent. Input layout: [fuel:u16][split:u16][image ‖ proof].
#![no_main]
use arena_npai::interp::{decode, run_full, Inputs};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() < 4 {
        return;
    }
    let fuel = u16::from_le_bytes([data[0], data[1]]) as u64;
    let split = (u16::from_le_bytes([data[2], data[3]]) as usize).min(data.len() - 4);
    let (image, proof) = data[4..].split_at(split);
    if let Some(p) = decode(image) {
        let (_, s) = run_full(
            &p,
            &Inputs {
                public: proof,
                claim: &proof[..proof.len() / 2],
                proof,
            },
            fuel,
            true,
        );
        assert!(s.fuel <= fuel);
        assert_eq!(s.mem.len(), p.mem_size as usize);
    }
});
