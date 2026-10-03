//! Decoder robustness: never panics; accepted images re-encode to exactly
//! the input bytes (decoding is canonical and trailing bytes are rejected).
#![no_main]
use arena_npai::interp::{decode, encode};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Some(p) = decode(data) {
        assert_eq!(encode(&p), data);
    }
});
