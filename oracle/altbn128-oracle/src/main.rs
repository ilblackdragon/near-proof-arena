//! Reference oracle for the three `alt_bn128_*` host semantics.
//!
//! A verbatim transcription of nearcore 44f7ae6c (2.13.4, PV86)
//! `runtime/near-vm-runner/src/logic/alt_bn128.rs` — the module that forwards every byte of decoding
//! and arithmetic to the `bn` crate — over `zeropool-bn` 0.5.11, the crate and version nearcore's own
//! `Cargo.toml:165` pins (`bn = { package = "zeropool-bn", version = "0.5.11", default-features =
//! false }`). The host bodies (`wasmtime_runner/logic.rs:932-1053`) contribute the argument order,
//! the charge order and the register write; those are reproduced here as pure functions of the
//! input bytes because the wasm-side plumbing is not arithmetic (the Lean side models it from
//! `Wasm/Host.lean`, and the arithmetic/decoding verdicts are what this oracle pins).
//!
//! Modes:
//!   altbn128-oracle <fn> <hexinput>
//!     prints `res <u64>` and, for the two register writers, `out <hex>`; a length error prints
//!     `err <msg>` with the message text `logic/alt_bn128.rs` produces.
//!   altbn128-oracle <fn> <hexinput> --raw
//!     prints only the register hex on success (`-` when nothing was written).
//!
//! The three hosts are `alt_bn128_g1_multiexp`, `alt_bn128_g1_sum`, `alt_bn128_pairing_check`
//! (`imports.rs:354-356`). Encoding is **little-endian**, unlike the EVM precompiles; see the module
//! docs of `logic/alt_bn128.rs:1-169` and the lane log for the full table.

use std::fmt;
use bn::Group;

// ---------------------------------------------------------------------------------------------
// `logic/alt_bn128.rs` — constants and the `InvalidInput` carrier
// ---------------------------------------------------------------------------------------------

const BOOL_SIZE: usize = 1;
const SCALAR_SIZE: usize = 256 / 8;
const POINT_SIZE: usize = SCALAR_SIZE * 2;

const G1_MULTIEXP_ELEMENT_SIZE: usize = POINT_SIZE + SCALAR_SIZE;
const G1_SUM_ELEMENT_SIZE: usize = BOOL_SIZE + POINT_SIZE;
const PAIRING_CHECK_ELEMENT_SIZE: usize = POINT_SIZE + POINT_SIZE * 2;

/// `logic/alt_bn128.rs:11-23` `InvalidInput`, whose `Display` is `HostError::AltBn128InvalidInput`'s
/// `AltBn128 invalid input: {msg}` (`logic/errors.rs:614`).
#[derive(Debug)]
struct InvalidInput {
    msg: String,
}

impl InvalidInput {
    /// `InvalidInput::new`: `format!("{msg}: {bad_value:X?}")`.
    fn new(msg: &str, bad_value: &[u8]) -> InvalidInput {
        // Rust's `{:X?}` for `[u8]`: unpadded uppercase hex, comma-space separated.
        let rendered = bad_value
            .iter()
            .map(|b| format!("{b:X}"))
            .collect::<Vec<_>>()
            .join(", ");
        InvalidInput {
            msg: format!("{msg}: [{rendered}]"),
        }
    }
}

impl fmt::Display for InvalidInput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AltBn128 invalid input: {}", self.msg)
    }
}

/// `stdx::as_chunks_exact`'s error text (`utils/stdx/src/lib.rs:89-96`), the `msg` that
/// `split_elements` wraps (`logic/alt_bn128.rs:26-30`).
fn split_error(slice_len: usize, chunk_size: usize) -> InvalidInput {
    InvalidInput {
        msg: format!(
            "slice of size {slice_len} cannot be precisely split into chunks of size {chunk_size}"
        ),
    }
}

/// `logic/alt_bn128.rs:26-30` `split_elements`, returning owned chunks for simplicity (the Rust
/// version borrows; the split and its error text are identical).
fn split_elements<const ELEMENT_SIZE: usize>(data: &[u8]) -> Result<Vec<[u8; ELEMENT_SIZE]>, InvalidInput> {
    if data.len() % ELEMENT_SIZE != 0 {
        return Err(split_error(data.len(), ELEMENT_SIZE));
    }
    Ok(data
        .chunks_exact(ELEMENT_SIZE)
        .map(|c| {
            let mut a = [0u8; ELEMENT_SIZE];
            a.copy_from_slice(c);
            a
        })
        .collect())
}

// ---------------------------------------------------------------------------------------------
// The three payloads — `logic/alt_bn128.rs:36-89`
// ---------------------------------------------------------------------------------------------

fn g1_multiexp(elements: &[[u8; G1_MULTIEXP_ELEMENT_SIZE]]) -> Result<[u8; POINT_SIZE], InvalidInput> {
    let mut decoded: Vec<(bn::G1, bn::Fr)> = Vec::with_capacity(elements.len());
    for chunk in elements {
        let (g1, fr) = chunk.split_at(POINT_SIZE);
        let g1 = decode_g1(g1)?;
        let fr = decode_fr(fr)?;
        decoded.push((g1, fr));
    }
    // `bn::G1::multiexp` filters out affine-zero items and runs Pippenger over the rest
    // (`zeropool-bn-0.5.11/src/lib.rs:405-414`); the Lean side reproduces the same *sum*, and the
    // verdict is compared against this oracle.
    let res = bn::G1::multiexp(&decoded);
    Ok(encode_g1(res))
}

fn g1_sum(elements: &[[u8; G1_SUM_ELEMENT_SIZE]]) -> Result<[u8; POINT_SIZE], InvalidInput> {
    let mut decoded: Vec<(bool, bn::G1)> = Vec::with_capacity(elements.len());
    for chunk in elements {
        let (sign, g1) = chunk.split_at(BOOL_SIZE);
        let sign = decode_bool(sign)?;
        let g1 = decode_g1(g1)?;
        decoded.push((sign, g1));
    }
    let res = decoded.iter().fold(bn::G1::zero(), |acc, &(sign, x)| {
        if sign {
            acc - x
        } else {
            acc + x
        }
    });
    Ok(encode_g1(res))
}

fn pairing_check(elements: &[[u8; PAIRING_CHECK_ELEMENT_SIZE]]) -> Result<bool, InvalidInput> {
    let mut decoded: Vec<(bn::G1, bn::G2)> = Vec::with_capacity(elements.len());
    for chunk in elements {
        let (g1, g2) = chunk.split_at(POINT_SIZE);
        let g1 = decode_g1(g1)?;
        let g2 = decode_g2(g2)?;
        decoded.push((g1, g2));
    }
    let res = bn::pairing_batch(&decoded) == bn::Gt::one();
    Ok(res)
}

// ---------------------------------------------------------------------------------------------
// The codec — `logic/alt_bn128.rs:91-169`
// ---------------------------------------------------------------------------------------------

fn encode_g1(val: bn::G1) -> [u8; POINT_SIZE] {
    let (x, y) = bn::AffineG1::from_jacobian(val)
        .map(|p| (p.x(), p.y()))
        .unwrap_or_else(|| (bn::Fq::zero(), bn::Fq::zero()));
    let x = encode_fq(x);
    let y = encode_fq(y);
    let mut out = [0u8; POINT_SIZE];
    out[..SCALAR_SIZE].copy_from_slice(&x);
    out[SCALAR_SIZE..].copy_from_slice(&y);
    out
}

fn encode_fq(val: bn::Fq) -> [u8; SCALAR_SIZE] {
    encode_u256(val.into_u256())
}

/// `encode_u256`: `lo.to_le_bytes() ‖ hi.to_le_bytes()`, where `U256([lo, hi])` are two `u128`
/// limbs (`logic/alt_bn128.rs:101-104`).
fn encode_u256(val: bn::arith::U256) -> [u8; SCALAR_SIZE] {
    let [lo, hi] = val.0;
    let mut out = [0u8; SCALAR_SIZE];
    out[..16].copy_from_slice(&lo.to_le_bytes());
    out[16..].copy_from_slice(&hi.to_le_bytes());
    out
}

fn decode_g1(raw: &[u8]) -> Result<bn::G1, InvalidInput> {
    let (x, y) = raw.split_at(SCALAR_SIZE);
    let x = decode_fq(x)?;
    let y = decode_fq(y)?;
    if x.is_zero() && y.is_zero() {
        Ok(bn::G1::zero())
    } else {
        bn::AffineG1::new(x, y)
            .map_err(|_| InvalidInput::new("invalid g1", raw))
            .map(bn::G1::from)
    }
}

fn decode_fq(raw: &[u8]) -> Result<bn::Fq, InvalidInput> {
    let val = decode_u256(raw);
    bn::Fq::from_u256(val).map_err(|_| InvalidInput::new("invalid fq", raw))
}

fn decode_g2(raw: &[u8]) -> Result<bn::G2, InvalidInput> {
    let (x, y) = raw.split_at(POINT_SIZE);
    let x = decode_fq2(x)?;
    let y = decode_fq2(y)?;
    if x.is_zero() && y.is_zero() {
        Ok(bn::G2::zero())
    } else {
        bn::AffineG2::new(x, y)
            .map_err(|_| InvalidInput::new("invalid g2", raw))
            .map(bn::G2::from)
    }
}

fn decode_fq2(raw: &[u8]) -> Result<bn::Fq2, InvalidInput> {
    let (real, imaginary) = raw.split_at(SCALAR_SIZE);
    let real = decode_fq(real)?;
    let imaginary = decode_fq(imaginary)?;
    Ok(bn::Fq2::new(real, imaginary))
}

fn decode_fr(raw: &[u8]) -> Result<bn::Fr, InvalidInput> {
    let val = decode_u256(raw);
    bn::Fr::new(val).ok_or_else(|| InvalidInput::new("invalid fr", raw))
}

/// `decode_u256`: `u128::from_le_bytes(lo) ‖ u128::from_le_bytes(hi)` (`logic/alt_bn128.rs:158-163`).
fn decode_u256(raw: &[u8]) -> bn::arith::U256 {
    let (lo, hi) = raw.split_at(16);
    let mut lo_b = [0u8; 16];
    let mut hi_b = [0u8; 16];
    lo_b.copy_from_slice(lo);
    hi_b.copy_from_slice(hi);
    bn::arith::U256([u128::from_le_bytes(lo_b), u128::from_le_bytes(hi_b)])
}

fn decode_bool(raw: &[u8]) -> Result<bool, InvalidInput> {
    match raw {
        [0] => Ok(false),
        [1] => Ok(true),
        _ => Err(InvalidInput::new("invalid bool", raw)),
    }
}

// ---------------------------------------------------------------------------------------------
// The host bodies' argument/charge shape, as a pure function of the input bytes
// ---------------------------------------------------------------------------------------------
//
// `wasmtime_runner/logic.rs:932-1053`:
//   * `alt_bn128_g1_multiexp(value_len, value_ptr, register_id)` — `pay_base`, read, split, pay_per,
//     decode, write register. Returns `()`.
//   * `alt_bn128_g1_sum(value_len, value_ptr, register_id)` — same shape. Returns `()`.
//   * `alt_bn128_pairing_check(value_len, value_ptr)` — `pay_base`, read, split, pay_per, decode.
//     Returns `u64`.
// The per-element count in all three is `elements.len()` *after* the split, i.e. the charge happens
// only once the split succeeded. A split failure therefore burns base + the read cost, and no
// per-element charge — the same order the Lean host arms implement.

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: altbn128-oracle <fn> <hexinput> [--raw]");
        std::process::exit(2);
    }
    let fname = &args[1];
    let hex = &args[2];
    let raw = args.iter().any(|a| a == "--raw");
    let data = match hex_decode(hex) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("bad hex: {e}");
            std::process::exit(2);
        }
    };

    match fname.as_str() {
        "alt_bn128_g1_multiexp" => match split_elements::<G1_MULTIEXP_ELEMENT_SIZE>(&data)
            .and_then(|e| g1_multiexp(&e))
        {
            Ok(out) => {
                if raw {
                    println!("{}", hex_encode(&out));
                } else {
                    println!("res 0");
                    println!("out {}", hex_encode(&out));
                }
            }
            Err(e) => {
                if raw {
                    println!("-");
                } else {
                    println!("err {}", e.msg);
                }
            }
        },
        "alt_bn128_g1_sum" => match split_elements::<G1_SUM_ELEMENT_SIZE>(&data)
            .and_then(|e| g1_sum(&e))
        {
            Ok(out) => {
                if raw {
                    println!("{}", hex_encode(&out));
                } else {
                    println!("res 0");
                    println!("out {}", hex_encode(&out));
                }
            }
            Err(e) => {
                if raw {
                    println!("-");
                } else {
                    println!("err {}", e.msg);
                }
            }
        },
        "alt_bn128_pairing_check" => match split_elements::<PAIRING_CHECK_ELEMENT_SIZE>(&data)
            .and_then(|e| pairing_check(&e))
        {
            Ok(v) => {
                // `wasmtime_runner/logic.rs:1051-1053`: `Ok(res as u64)`.
                println!("res {}", if v { 1 } else { 0 });
                if raw {
                    // no register for this host
                }
            }
            Err(e) => {
                if raw {
                    println!("-");
                } else {
                    println!("err {}", e.msg);
                }
            }
        },
        other => {
            eprintln!("unknown fn {other}");
            std::process::exit(2);
        }
    }
}

fn hex_decode(s: &str) -> Result<Vec<u8>, String> {
    if s.len() % 2 != 0 {
        return Err("odd length".into());
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).map_err(|e| e.to_string()))
        .collect()
}

fn hex_encode(d: &[u8]) -> String {
    d.iter().map(|b| format!("{b:02x}")).collect()
}
