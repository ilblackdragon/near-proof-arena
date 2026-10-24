//! Reference oracle for the BLS12-381 host semantics.
//!
//! A verbatim transcription of nearcore 44f7ae6c
//! `runtime/near-vm-runner/src/logic/bls12381.rs` over `blst` 0.3.11 — the exact crate version
//! nearcore's own `Cargo.lock` pins (`blst = { version = "0.3.11", features = ["portable"] }`,
//! nearcore `Cargo.toml:164`). The only thing this binary does *not* reproduce is the wasm-side
//! plumbing (`pay_base`, `get_memory_or_register`, `registers.set`), which is not arithmetic: the
//! Lean side models those from `Wasm/Host.lean`, and the shared arithmetic/decoding verdicts are
//! what this oracle pins.
//!
//! Modes:
//!   bls-oracle <fn> <hexinput> [version]
//!     prints one line: `res <u64>` and, when the function succeeded and wrote a register,
//!     `out <hex>`. A `BLS12381InvalidInput` length error prints `err BLS12381InvalidInput <msg>`.
//!   bls-oracle <fn> <hexinput> [version] --raw
//!     prints only the register hex on success (`-` when nothing was written).
//!
//! `version` is 0 (PV86: `bls12381_not_in_group_fix = false`, `parameters.snap:289`) or 1
//! (post-NEP-488). Default 0, because PV86 is the pinned protocol.

use std::ptr::null;

const BLS_BOOL_SIZE: usize = 1;
const BLS_SCALAR_SIZE: usize = 32;
const BLS_FP_SIZE: usize = 48;
const BLS_FP2_SIZE: usize = 96;
const BLS_P1_SIZE: usize = 96;
const BLS_P2_SIZE: usize = 192;
const BLS_P1_COMPRESS_SIZE: usize = 48;
const BLS_P2_COMPRESS_SIZE: usize = 96;

pub const BLS12381_NOT_IN_GROUP_FIX_VERSION: u32 = 1;

/// `HostError::BLS12381InvalidInput` as `logic/bls12381.rs` raises it, carrying the message text
/// produced by `check_input_size`.
struct InvalidInput(String);

fn check_input_size(data: &[u8], item_size: usize, fn_name: &str) -> Result<(), InvalidInput> {
    if data.len() % item_size != 0 {
        return Err(InvalidInput(format!(
            "Incorrect input length for {}: {} is not divisible by {}",
            fn_name,
            data.len(),
            item_size
        )));
    }
    Ok(())
}

// --- the `bls12381_fn!` body for G1 ------------------------------------------------------

fn parse_p1(point_data: &[u8], version: u32) -> Option<blst::blst_p1> {
    if point_data[0] & 0x80 != 0 {
        return None;
    }
    let mut pk_aff = blst::blst_p1_affine::default();
    let error_code = unsafe { blst::blst_p1_deserialize(&mut pk_aff, point_data.as_ptr()) };
    let success = error_code == blst::BLST_ERROR::BLST_SUCCESS
        || (version >= BLS12381_NOT_IN_GROUP_FIX_VERSION
            && error_code == blst::BLST_ERROR::BLST_POINT_NOT_IN_GROUP);
    if !success {
        return None;
    }
    let mut pk = blst::blst_p1::default();
    unsafe { blst::blst_p1_from_affine(&mut pk, &pk_aff) };
    Some(pk)
}

fn parse_p2(point_data: &[u8], version: u32) -> Option<blst::blst_p2> {
    if point_data[0] & 0x80 != 0 {
        return None;
    }
    let mut pk_aff = blst::blst_p2_affine::default();
    let error_code = unsafe { blst::blst_p2_deserialize(&mut pk_aff, point_data.as_ptr()) };
    let success = error_code == blst::BLST_ERROR::BLST_SUCCESS
        || (version >= BLS12381_NOT_IN_GROUP_FIX_VERSION
            && error_code == blst::BLST_ERROR::BLST_POINT_NOT_IN_GROUP);
    if !success {
        return None;
    }
    let mut pk = blst::blst_p2::default();
    unsafe { blst::blst_p2_from_affine(&mut pk, &pk_aff) };
    Some(pk)
}

fn serialize_p1(res_pk: &blst::blst_p1) -> Vec<u8> {
    let mut res_affine = blst::blst_p1_affine::default();
    unsafe { blst::blst_p1_to_affine(&mut res_affine, res_pk) };
    let mut res = [0u8; BLS_P1_SIZE];
    unsafe { blst::blst_p1_affine_serialize(res.as_mut_ptr(), &res_affine) };
    res.to_vec()
}

fn serialize_p2(res_pk: &blst::blst_p2) -> Vec<u8> {
    let mut res_affine = blst::blst_p2_affine::default();
    unsafe { blst::blst_p2_to_affine(&mut res_affine, res_pk) };
    let mut res = [0u8; BLS_P2_SIZE];
    unsafe { blst::blst_p2_affine_serialize(res.as_mut_ptr(), &res_affine) };
    res.to_vec()
}

fn p1_sum(data: &[u8], version: u32) -> Result<Option<Vec<u8>>, InvalidInput> {
    const ITEM_SIZE: usize = BLS_BOOL_SIZE + BLS_P1_SIZE;
    check_input_size(data, ITEM_SIZE, "bls12381_p1_sum")?;
    let mut res_pk = blst::blst_p1::default();
    for item_data in data.chunks_exact(ITEM_SIZE) {
        let (sign_data, point_data) = item_data.split_at(BLS_BOOL_SIZE);
        let mut pk = match parse_p1(point_data, version) {
            Some(pk) => pk,
            None => return Ok(None),
        };
        let sign = sign_data[0];
        if sign == 1 {
            unsafe { blst::blst_p1_cneg(&mut pk, true) };
        } else if sign != 0 {
            return Ok(None);
        }
        unsafe { blst::blst_p1_add_or_double(&mut res_pk, &res_pk, &pk) };
    }
    Ok(Some(serialize_p1(&res_pk)))
}

fn p2_sum(data: &[u8], version: u32) -> Result<Option<Vec<u8>>, InvalidInput> {
    const ITEM_SIZE: usize = BLS_BOOL_SIZE + BLS_P2_SIZE;
    check_input_size(data, ITEM_SIZE, "bls12381_p2_sum")?;
    let mut res_pk = blst::blst_p2::default();
    for item_data in data.chunks_exact(ITEM_SIZE) {
        let (sign_data, point_data) = item_data.split_at(BLS_BOOL_SIZE);
        let mut pk = match parse_p2(point_data, version) {
            Some(pk) => pk,
            None => return Ok(None),
        };
        let sign = sign_data[0];
        if sign == 1 {
            unsafe { blst::blst_p2_cneg(&mut pk, true) };
        } else if sign != 0 {
            return Ok(None);
        }
        unsafe { blst::blst_p2_add_or_double(&mut res_pk, &res_pk, &pk) };
    }
    Ok(Some(serialize_p2(&res_pk)))
}

fn g1_multiexp(data: &[u8], version: u32) -> Result<Option<Vec<u8>>, InvalidInput> {
    const ITEM_SIZE: usize = BLS_P1_SIZE + BLS_SCALAR_SIZE;
    check_input_size(data, ITEM_SIZE, "bls12381_p1_multiexp")?;
    let mut res_pk = blst::blst_p1::default();
    for item_data in data.chunks_exact(ITEM_SIZE) {
        let (point_data, scalar_data) = item_data.split_at(BLS_P1_SIZE);
        let pk = match parse_p1(point_data, version) {
            Some(pk) => pk,
            None => return Ok(None),
        };
        if unsafe { blst::blst_p1_in_g1(&pk) } != true {
            return Ok(None);
        }
        let mut pk_mul = blst::blst_p1::default();
        unsafe { blst::blst_p1_mult(&mut pk_mul, &pk, scalar_data.as_ptr(), BLS_SCALAR_SIZE * 8) };
        unsafe { blst::blst_p1_add_or_double(&mut res_pk, &res_pk, &pk_mul) };
    }
    Ok(Some(serialize_p1(&res_pk)))
}

fn g2_multiexp(data: &[u8], version: u32) -> Result<Option<Vec<u8>>, InvalidInput> {
    const ITEM_SIZE: usize = BLS_P2_SIZE + BLS_SCALAR_SIZE;
    check_input_size(data, ITEM_SIZE, "bls12381_p2_multiexp")?;
    let mut res_pk = blst::blst_p2::default();
    for item_data in data.chunks_exact(ITEM_SIZE) {
        let (point_data, scalar_data) = item_data.split_at(BLS_P2_SIZE);
        let pk = match parse_p2(point_data, version) {
            Some(pk) => pk,
            None => return Ok(None),
        };
        if unsafe { blst::blst_p2_in_g2(&pk) } != true {
            return Ok(None);
        }
        let mut pk_mul = blst::blst_p2::default();
        unsafe { blst::blst_p2_mult(&mut pk_mul, &pk, scalar_data.as_ptr(), BLS_SCALAR_SIZE * 8) };
        unsafe { blst::blst_p2_add_or_double(&mut res_pk, &res_pk, &pk_mul) };
    }
    Ok(Some(serialize_p2(&res_pk)))
}

fn p1_decompress(data: &[u8], version: u32) -> Result<Option<Vec<u8>>, InvalidInput> {
    const ITEM_SIZE: usize = BLS_P1_COMPRESS_SIZE;
    check_input_size(data, ITEM_SIZE, "bls12381_p1_decompress")?;
    let mut res = Vec::<u8>::new();
    for item_data in data.chunks_exact(ITEM_SIZE) {
        let pk_ser = if item_data[0] & 0x80 != 0 {
            if version >= BLS12381_NOT_IN_GROUP_FIX_VERSION {
                let mut pk = blst::blst_p1_affine::default();
                let err = unsafe { blst::blst_p1_uncompress(&mut pk, item_data.as_ptr()) };
                if err != blst::BLST_ERROR::BLST_SUCCESS
                    && err != blst::BLST_ERROR::BLST_POINT_NOT_IN_GROUP
                {
                    return Ok(None);
                }
                let mut out = [0u8; BLS_P1_SIZE];
                unsafe { blst::blst_p1_affine_serialize(out.as_mut_ptr(), &pk) };
                out.to_vec()
            } else {
                let pk_res = blst::min_pk::PublicKey::uncompress(item_data);
                match pk_res {
                    Ok(pk) => pk.serialize().to_vec(),
                    Err(_) => return Ok(None),
                }
            }
        } else {
            return Ok(None);
        };
        res.extend_from_slice(&pk_ser);
    }
    Ok(Some(res))
}

fn p2_decompress(data: &[u8], version: u32) -> Result<Option<Vec<u8>>, InvalidInput> {
    const ITEM_SIZE: usize = BLS_P2_COMPRESS_SIZE;
    check_input_size(data, ITEM_SIZE, "bls12381_p2_decompress")?;
    let mut res = Vec::<u8>::new();
    for item_data in data.chunks_exact(ITEM_SIZE) {
        let pk_ser = if item_data[0] & 0x80 != 0 {
            if version >= BLS12381_NOT_IN_GROUP_FIX_VERSION {
                let mut pk = blst::blst_p2_affine::default();
                let err = unsafe { blst::blst_p2_uncompress(&mut pk, item_data.as_ptr()) };
                if err != blst::BLST_ERROR::BLST_SUCCESS
                    && err != blst::BLST_ERROR::BLST_POINT_NOT_IN_GROUP
                {
                    return Ok(None);
                }
                let mut out = [0u8; BLS_P2_SIZE];
                unsafe { blst::blst_p2_affine_serialize(out.as_mut_ptr(), &pk) };
                out.to_vec()
            } else {
                let sig_res = blst::min_pk::Signature::uncompress(item_data);
                match sig_res {
                    Ok(sig) => sig.serialize().to_vec(),
                    Err(_) => return Ok(None),
                }
            }
        } else {
            return Ok(None);
        };
        res.extend_from_slice(&pk_ser);
    }
    Ok(Some(res))
}

fn read_fp_point(item_data: &[u8]) -> Option<blst::blst_fp> {
    let mut fp_point = blst::blst_fp::default();
    unsafe { blst::blst_fp_from_bendian(&mut fp_point, item_data.as_ptr()) };
    let mut fp_row = [0u8; BLS_FP_SIZE];
    unsafe { blst::blst_bendian_from_fp(fp_row.as_mut_ptr(), &fp_point) };
    for j in 0..BLS_FP_SIZE {
        if fp_row[j] != item_data[j] {
            return None;
        }
    }
    Some(fp_point)
}

fn read_fp2_point(item_data: &[u8]) -> Option<blst::blst_fp2> {
    let mut c_fp1 = [blst::blst_fp::default(); 2];
    unsafe {
        blst::blst_fp_from_bendian(&mut c_fp1[1], item_data[..BLS_FP_SIZE].as_ptr());
        blst::blst_fp_from_bendian(&mut c_fp1[0], item_data[BLS_FP_SIZE..].as_ptr());
    }
    let mut fp_row = [0u8; BLS_FP_SIZE];
    unsafe { blst::blst_bendian_from_fp(fp_row.as_mut_ptr(), &c_fp1[0]) };
    for j in BLS_FP_SIZE..BLS_FP2_SIZE {
        if fp_row[j - BLS_FP_SIZE] != item_data[j] {
            return None;
        }
    }
    unsafe { blst::blst_bendian_from_fp(fp_row.as_mut_ptr(), &c_fp1[1]) };
    for j in 0..BLS_FP_SIZE {
        if fp_row[j] != item_data[j] {
            return None;
        }
    }
    Some(blst::blst_fp2 { fp: c_fp1 })
}

fn map_fp_to_g1(data: &[u8], _version: u32) -> Result<Option<Vec<u8>>, InvalidInput> {
    const ITEM_SIZE: usize = BLS_FP_SIZE;
    check_input_size(data, ITEM_SIZE, "bls12381_map_fp_to_g1")?;
    let mut res_concat: Vec<u8> = Vec::new();
    for item_data in data.chunks_exact(ITEM_SIZE) {
        let fp_point = match read_fp_point(item_data) {
            Some(p) => p,
            None => return Ok(None),
        };
        let mut g_point = blst::blst_p1::default();
        unsafe { blst::blst_map_to_g1(&mut g_point, &fp_point, null()) };
        let mut res = serialize_p1(&g_point);
        res_concat.append(&mut res);
    }
    Ok(Some(res_concat))
}

fn map_fp2_to_g2(data: &[u8], _version: u32) -> Result<Option<Vec<u8>>, InvalidInput> {
    const ITEM_SIZE: usize = BLS_FP2_SIZE;
    check_input_size(data, ITEM_SIZE, "bls12381_map_fp2_to_g2")?;
    let mut res_concat: Vec<u8> = Vec::new();
    for item_data in data.chunks_exact(ITEM_SIZE) {
        let fp_point = match read_fp2_point(item_data) {
            Some(p) => p,
            None => return Ok(None),
        };
        let mut g_point = blst::blst_p2::default();
        unsafe { blst::blst_map_to_g2(&mut g_point, &fp_point, null()) };
        let mut res = serialize_p2(&g_point);
        res_concat.append(&mut res);
    }
    Ok(Some(res_concat))
}

fn pairing_check(data: &[u8]) -> Result<u64, InvalidInput> {
    const ITEM_SIZE: usize = BLS_P1_SIZE + BLS_P2_SIZE;
    check_input_size(data, ITEM_SIZE, "bls12381_pairing_check")?;
    let elements_count = data.len() / ITEM_SIZE;
    let mut blst_g1_list: Vec<blst::blst_p1_affine> =
        vec![blst::blst_p1_affine::default(); elements_count];
    let mut blst_g2_list: Vec<blst::blst_p2_affine> =
        vec![blst::blst_p2_affine::default(); elements_count];

    for (i, item_data) in data.chunks_exact(ITEM_SIZE).enumerate() {
        let (point1_data, point2_data) = item_data.split_at(BLS_P1_SIZE);
        if point1_data[0] & 0x80 != 0 {
            return Ok(1);
        }
        let error_code =
            unsafe { blst::blst_p1_deserialize(&mut blst_g1_list[i], point1_data.as_ptr()) };
        if error_code != blst::BLST_ERROR::BLST_SUCCESS {
            return Ok(1);
        }
        let g1_check = unsafe { blst::blst_p1_affine_in_g1(&blst_g1_list[i]) };
        if g1_check == false {
            return Ok(1);
        }
        if point2_data[0] & 0x80 != 0 {
            return Ok(1);
        }
        let error_code =
            unsafe { blst::blst_p2_deserialize(&mut blst_g2_list[i], point2_data.as_ptr()) };
        if error_code != blst::BLST_ERROR::BLST_SUCCESS {
            return Ok(1);
        }
        let g2_check = unsafe { blst::blst_p2_affine_in_g2(&blst_g2_list[i]) };
        if g2_check == false {
            return Ok(1);
        }
    }

    let mut pairing_fp12 = blst::blst_fp12::default();
    for i in 0..elements_count {
        pairing_fp12 *= blst::blst_fp12::miller_loop(&blst_g2_list[i], &blst_g1_list[i]);
    }
    pairing_fp12 = pairing_fp12.final_exp();
    let pairing_res = unsafe { blst::blst_fp12_is_one(&pairing_fp12) };
    if pairing_res {
        Ok(0)
    } else {
        Ok(2)
    }
}

/// `serialize_p1` / `serialize_p2` of an arbitrary *deserialized* affine point, for tests that want
/// the raw G1/G2 encode/decode round trip (not a host function).
fn raw_g1_roundtrip(data: &[u8], version: u32) -> Option<Vec<u8>> {
    if data.len() != BLS_P1_SIZE {
        return None;
    }
    let mut pk_aff = blst::blst_p1_affine::default();
    let e = unsafe { blst::blst_p1_deserialize(&mut pk_aff, data.as_ptr()) };
    let ok = e == blst::BLST_ERROR::BLST_SUCCESS
        || (version >= BLS12381_NOT_IN_GROUP_FIX_VERSION
            && e == blst::BLST_ERROR::BLST_POINT_NOT_IN_GROUP);
    if !ok {
        return None;
    }
    let mut out = [0u8; BLS_P1_SIZE];
    unsafe { blst::blst_p1_affine_serialize(out.as_mut_ptr(), &pk_aff) };
    Some(out.to_vec())
}

fn raw_g2_roundtrip(data: &[u8], version: u32) -> Option<Vec<u8>> {
    if data.len() != BLS_P2_SIZE {
        return None;
    }
    let mut pk_aff = blst::blst_p2_affine::default();
    let e = unsafe { blst::blst_p2_deserialize(&mut pk_aff, data.as_ptr()) };
    let ok = e == blst::BLST_ERROR::BLST_SUCCESS
        || (version >= BLS12381_NOT_IN_GROUP_FIX_VERSION
            && e == blst::BLST_ERROR::BLST_POINT_NOT_IN_GROUP);
    if !ok {
        return None;
    }
    let mut out = [0u8; BLS_P2_SIZE];
    unsafe { blst::blst_p2_affine_serialize(out.as_mut_ptr(), &pk_aff) };
    Some(out.to_vec())
}

/// `blst_p1_affine_in_g1` / `blst_p2_affine_in_g2` on a *deserialized* affine point: the subgroup
/// predicate the multiexp hosts use.
fn in_g1(data: &[u8], version: u32) -> u64 {
    match raw_g1_roundtrip(data, version) {
        None => 1,
        Some(_) => {
            let mut pk_aff = blst::blst_p1_affine::default();
            let _ = unsafe { blst::blst_p1_deserialize(&mut pk_aff, data.as_ptr()) };
            u64::from(unsafe { blst::blst_p1_affine_in_g1(&pk_aff) } != true)
        }
    }
}

fn in_g2(data: &[u8], version: u32) -> u64 {
    match raw_g2_roundtrip(data, version) {
        None => 1,
        Some(_) => {
            let mut pk_aff = blst::blst_p2_affine::default();
            let _ = unsafe { blst::blst_p2_deserialize(&mut pk_aff, data.as_ptr()) };
            u64::from(unsafe { blst::blst_p2_affine_in_g2(&pk_aff) } != true)
        }
    }
}

fn hex(s: &str) -> Vec<u8> {
    let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    if s.len() % 2 != 0 {
        panic!("odd hex length");
    }
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("hex"))
        .collect()
}

fn tohex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("usage: bls-oracle <fn> <hexinput> [version] [--raw]");
        std::process::exit(2);
    }
    let raw = args.iter().any(|a| a == "--raw");
    let argv: Vec<&String> = args.iter().filter(|a| *a != "--raw").collect();
    let fname = argv[0].as_str();
    let data = hex(argv.get(1).map(|s| s.as_str()).unwrap_or(""));
    let version: u32 = argv.get(2).map(|s| s.parse().expect("version")).unwrap_or(0);

    // functions returning Result<Option<Vec<u8>>>: register writers
    let writer: Option<Result<Option<Vec<u8>>, InvalidInput>> = match fname {
        "bls12381_p1_sum" => Some(p1_sum(&data, version)),
        "bls12381_p2_sum" => Some(p2_sum(&data, version)),
        "bls12381_g1_multiexp" => Some(g1_multiexp(&data, version)),
        "bls12381_g2_multiexp" => Some(g2_multiexp(&data, version)),
        "bls12381_map_fp_to_g1" => Some(map_fp_to_g1(&data, version)),
        "bls12381_map_fp2_to_g2" => Some(map_fp2_to_g2(&data, version)),
        "bls12381_p1_decompress" => Some(p1_decompress(&data, version)),
        "bls12381_p2_decompress" => Some(p2_decompress(&data, version)),
        _ => None,
    };

    if let Some(res) = writer {
        match res {
            Err(InvalidInput(msg)) => {
                if raw {
                    println!("-");
                } else {
                    println!("err BLS12381InvalidInput {}", msg);
                }
            }
            Ok(None) => {
                if raw {
                    println!("-");
                } else {
                    println!("res 1");
                }
            }
            Ok(Some(out)) => {
                if raw {
                    println!("{}", tohex(&out));
                } else {
                    println!("res 0");
                    println!("out {}", tohex(&out));
                }
            }
        }
        return;
    }

    match fname {
        "bls12381_pairing_check" => match pairing_check(&data) {
            Err(InvalidInput(msg)) => println!("err BLS12381InvalidInput {}", msg),
            Ok(r) => println!("res {}", r),
        },
        "raw_g1" => match raw_g1_roundtrip(&data, version) {
            None => println!("-"),
            Some(o) => println!("{}", tohex(&o)),
        },
        "raw_g2" => match raw_g2_roundtrip(&data, version) {
            None => println!("-"),
            Some(o) => println!("{}", tohex(&o)),
        },
        "in_g1" => println!("res {}", in_g1(&data, version)),
        "in_g2" => println!("res {}", in_g2(&data, version)),
        other => {
            eprintln!("unknown fn {}", other);
            std::process::exit(2);
        }
    }
}
