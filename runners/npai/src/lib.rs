//! `arena-npai`: the judge-owned NPAI v1 interpreter and tools.
//!
//! * [`interp`] — **TCB**. Transcription of `formal-core/ArenaCore/Interp.lean`;
//!   the only code whose behaviour a checked certificate relies on.
//! * [`asm`] — assembler/disassembler for backend authors (not TCB).
//! * [`report`] — hex/JSON rendering in the exact format of the Lean
//!   reference executable `arena-interp-ref` (used by differential tests and
//!   as `npai-verify` diagnostics; never affects an outcome).
//!
//! See `runners/npai/README.md` and `docs/INTERP_SPEC.md`.
#![forbid(unsafe_code)]

pub mod asm;
pub mod interp;

pub mod report {
    use crate::interp::Outcome;

    pub fn to_hex(b: &[u8]) -> String {
        const D: &[u8; 16] = b"0123456789abcdef";
        let mut s = String::with_capacity(b.len() * 2);
        for x in b {
            s.push(D[(x >> 4) as usize] as char);
            s.push(D[(x & 15) as usize] as char);
        }
        s
    }

    pub fn from_hex(s: &str) -> Option<Vec<u8>> {
        let s = s.as_bytes();
        if !s.len().is_multiple_of(2) {
            return None;
        }
        let v = |c: u8| (c as char).to_digit(16).map(|d| d as u8);
        s.chunks_exact(2)
            .map(|p| Some(v(p[0])? * 16 + v(p[1])?))
            .collect()
    }

    /// Byte-identical to `expectJson` in `formal-core/InterpRef.lean`.
    pub fn expect_json(r: &Option<(Outcome, u64, Vec<u8>, Vec<u8>)>) -> String {
        match r {
            None => "{\"outcome\":\"decode_error\"}".to_string(),
            Some((o, f, a, b)) => format!(
                "{{\"outcome\":\"{}\",\"fuel_used\":{},\"out0\":\"{}\",\"out1\":\"{}\"}}",
                o.as_str(),
                f,
                to_hex(a),
                to_hex(b)
            ),
        }
    }
}
