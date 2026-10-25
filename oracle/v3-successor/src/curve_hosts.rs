//! `NEAR_SUCCESSOR_SCENARIO=curve-hosts`: whole-chunk traffic that calls every curve host
//! (`alt_bn128_*`, `bls12381_*`, `p256_verify`, `ecrecover`) through `contracts/curvehosts.wat`.
//!
//! Inputs are *constructed* here with the same libraries nearcore links (zeropool-bn, blst, p256,
//! near-crypto's secp256k1), but only as inputs: every output, return code, error and gas figure in
//! the fixtures is what the pinned nearcore produced when it executed the chunk. A step's label names
//! the input class, never an expected result: `pos` = well-formed valid input, `neg` = malformed or
//! invalid input (whether nearcore answers with a host error or a failure return code), `edge` =
//! accepted-or-not corner cases (non-subgroup points in sums / decompression, scalars >= r, the (0, ±2) point,
//! empty / over-long p256 prehashes).
//!
//! Encodings (pinned `runtime/near-vm-runner/src/logic/{alt_bn128,bls12381}.rs`):
//! * alt_bn128: `Fq`/`Fr` are 32-byte little-endian; G1 = x‖y, G2 = (x.re‖x.im)‖(y.re‖y.im),
//!   `(0,0)` is the identity;
//! * BLS12-381: `Fp` is 48-byte big-endian, `Fp2` = c1‖c0, uncompressed points as blst serializes
//!   them (0x40 flag = infinity), scalars 32-byte little-endian.

use bn::{AffineG1, AffineG2, Fq, Fq2, Fr, G1, G2, Group};
use sha2::Digest;
use std::sync::OnceLock;

pub const ACCOUNT_A: &str = "s0curvehosts";
pub const ACCOUNT_B: &str = "s2curvehosts";
pub const CODE_NAME: &str = "curvehosts";

/// The contract bytes (wat compiled with the `wat` version of nearcore's lock).
pub fn code() -> &'static [u8] {
    static CODE: OnceLock<Vec<u8>> = OnceLock::new();
    CODE.get_or_init(|| wat::parse_str(include_str!("../contracts/curvehosts.wat")).expect("curvehosts.wat"))
}

pub struct Step {
    pub label: String,
    pub method: &'static str,
    pub args: Vec<u8>,
    pub tgas: u64,
}

pub fn steps() -> &'static [Step] {
    static STEPS: OnceLock<Vec<Step>> = OnceLock::new();
    STEPS.get_or_init(build)
}

// ---------------------------------------------------------------------------------------------
// byte helpers

fn hex32_be_to_le(h: &str) -> [u8; 32] {
    let mut b: [u8; 32] = hex::decode(h).unwrap().try_into().unwrap();
    b.reverse();
    b
}
fn hex48(h: &str) -> [u8; 48] {
    hex::decode(h).unwrap().try_into().unwrap()
}
/// big-endian a + b (same length, no overflow beyond the width)
fn add_be(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; a.len()];
    let mut carry = 0u16;
    for i in (0..a.len()).rev() {
        let s = a[i] as u16 + b[i] as u16 + carry;
        out[i] = s as u8;
        carry = s >> 8;
    }
    assert_eq!(carry, 0);
    out
}
/// big-endian a - b, a >= b
fn sub_be(a: &[u8], b: &[u8]) -> Vec<u8> {
    let mut out = vec![0u8; a.len()];
    let mut borrow = 0i16;
    for i in (0..a.len()).rev() {
        let mut d = a[i] as i16 - b[i] as i16 - borrow;
        borrow = if d < 0 { d += 256; 1 } else { 0 };
        out[i] = d as u8;
    }
    assert_eq!(borrow, 0);
    out
}
fn cat(parts: &[&[u8]]) -> Vec<u8> {
    parts.concat()
}
fn digest(tag: &str) -> [u8; 32] {
    sha2::Sha256::digest(tag.as_bytes()).into()
}

// ---------------------------------------------------------------------------------------------
// alt_bn128

/// field modulus p and group order r (big-endian hex)
const BN_P: &str = "30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47";
const BN_R: &str = "30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001";

fn u256_le(v: bn::arith::U256) -> [u8; 32] {
    let mut o = [0u8; 32];
    o[..16].copy_from_slice(&v.0[0].to_le_bytes());
    o[16..].copy_from_slice(&v.0[1].to_le_bytes());
    o
}
fn fq(v: Fq) -> [u8; 32] {
    u256_le(v.into_u256())
}
fn fq_n(n: u64) -> Fq {
    Fq::from_str(&n.to_string()).unwrap()
}
fn fr_n(n: u64) -> Fr {
    Fr::from_str(&n.to_string()).unwrap()
}
fn fr_le(f: Fr) -> [u8; 32] {
    u256_le(f.into_u256())
}
fn bn_g1(p: G1) -> Vec<u8> {
    match AffineG1::from_jacobian(p) {
        Some(a) => cat(&[&fq(a.x()), &fq(a.y())]),
        None => vec![0; 64],
    }
}
fn fq2(v: Fq2) -> Vec<u8> {
    cat(&[&fq(v.real()), &fq(v.imaginary())])
}
fn bn_g2(p: G2) -> Vec<u8> {
    match AffineG2::from_jacobian(p) {
        Some(a) => cat(&[&fq2(a.x()), &fq2(a.y())]),
        None => vec![0; 128],
    }
}
fn bn_g1k(k: u64) -> Vec<u8> {
    bn_g1(G1::one() * fr_n(k))
}
fn bn_g2k(k: u64) -> Vec<u8> {
    bn_g2(G2::one() * fr_n(k))
}
/// a point on the alt_bn128 twist that is not in the order-r subgroup (G2 has a cofactor)
fn bn_g2_not_in_subgroup() -> Vec<u8> {
    for k in 1u64.. {
        let x = Fq2::new(fq_n(k), Fq::one());
        let rhs = x * x * x + G2::b();
        if let Some(y) = rhs.sqrt() {
            assert!(y * y == rhs);
            if AffineG2::new(x, y).is_err() {
                return cat(&[&fq2(x), &fq2(y)]);
            }
        }
    }
    unreachable!()
}

fn alt_bn128(s: &mut Vec<Step>) {
    let p_le = hex32_be_to_le(BN_P);
    let r_le = hex32_be_to_le(BN_R);
    let g = bn_g1k(1);
    let neg_g = bn_g1(-G1::one());
    let off_curve = cat(&[&fq(fq_n(1)), &fq(fq_n(3))]);
    // x = p (non-canonical encoding of 0), y = 2: decode_fq rejects before the curve check
    let x_is_p = cat(&[&p_le, &fq(fq_n(2))]);
    // G with x + p: the same residue, non-canonical
    let mut gx_plus_p = add_be(&{ let mut b = g[..32].to_vec(); b.reverse(); b }, &{ let mut b = p_le.to_vec(); b.reverse(); b });
    gx_plus_p.reverse();
    let g_noncanon = cat(&[&gx_plus_p, &g[32..]]);
    let zero = vec![0u8; 64];

    // g1_sum: [(sign u8, G1 64 B)]
    let sum = |s: &mut Vec<Step>, case: &str, args: Vec<u8>| push(s, "alt_bn128_g1_sum", case, args, 100);
    sum(s, "pos.empty", vec![]);
    sum(s, "pos.g+2g-g", cat(&[&[0], &g, &[0], &bn_g1k(2), &[1], &g]));
    sum(s, "pos.identity", cat(&[&[0], &zero, &[1], &zero]));
    sum(s, "pos.p-p", cat(&[&[0], &bn_g1k(7), &[1], &bn_g1k(7)]));
    sum(s, "pos.g+neg_g", cat(&[&[0], &g, &[0], &neg_g]));
    sum(s, "neg.len64", g.clone());
    sum(s, "neg.len66", cat(&[&[0], &g, &[0]]));
    sum(s, "neg.sign2", cat(&[&[0], &g, &[2], &g]));
    sum(s, "neg.off_curve", cat(&[&[0], &off_curve]));
    sum(s, "neg.x_is_p", cat(&[&[0], &x_is_p]));
    sum(s, "neg.x_noncanonical", cat(&[&[0], &g_noncanon]));
    push(s, "alt_bn128_g1_sum_reg", "pos.register_input", cat(&[&[0], &g, &[0], &bn_g1k(3)]), 100);
    push(s, "alt_bn128_g1_sum_reg", "neg.register_input_len", cat(&[&[0], &g, &[9]]), 100);

    // g1_multiexp: [(G1 64 B, Fr 32 B LE)]
    let mexp = |s: &mut Vec<Step>, case: &str, args: Vec<u8>| push(s, "alt_bn128_g1_multiexp", case, args, 100);
    mexp(s, "pos.empty", vec![]);
    mexp(s, "pos.5g+7(2g)", cat(&[&g, &fr_le(fr_n(5)), &bn_g1k(2), &fr_le(fr_n(7))]));
    mexp(s, "pos.scalar0", cat(&[&g, &[0; 32]]));
    mexp(s, "pos.scalar_r-1", cat(&[&bn_g1k(3), &fr_le(-Fr::one())]));
    mexp(s, "pos.identity_point", cat(&[&zero, &fr_le(fr_n(11))]));
    mexp(s, "neg.scalar_r", cat(&[&g, &r_le]));
    mexp(s, "neg.scalar_max", cat(&[&g, &[0xff; 32]]));
    mexp(s, "neg.off_curve", cat(&[&off_curve, &fr_le(fr_n(2))]));
    mexp(s, "neg.x_noncanonical", cat(&[&g_noncanon, &fr_le(fr_n(2))]));
    mexp(s, "neg.len95", cat(&[&g, &[1; 31]]));
    mexp(s, "neg.second_bad", cat(&[&g, &fr_le(fr_n(2)), &off_curve, &fr_le(fr_n(2))]));
    push(s, "alt_bn128_g1_multiexp_reg", "pos.register_input", cat(&[&g, &fr_le(fr_n(9))]), 100);
    push(s, "alt_bn128_g1_multiexp_oob", "neg.memory_oob", vec![], 100);
    // 3 elements: base 0.713 + 3 x 0.32 Tgas > 1 Tgas prepaid at the per-element charge
    push(s, "alt_bn128_g1_multiexp", "neg.gas_at_element_charge",
        cat(&[&g, &fr_le(fr_n(2)), &g, &fr_le(fr_n(3)), &g, &fr_le(fr_n(4))]), 1);

    // pairing_check: [(G1 64 B, G2 128 B)]
    let q = bn_g2k(1);
    let pc = |s: &mut Vec<Step>, case: &str, args: Vec<u8>| push(s, "alt_bn128_pairing_check", case, args, 100);
    pc(s, "pos.empty", vec![]);
    pc(s, "pos.e(5g,q)e(-g,5q)", cat(&[&bn_g1k(5), &q, &neg_g, &bn_g2k(5)]));
    pc(s, "pos.e(g,q)", cat(&[&g, &q]));
    pc(s, "pos.identities", cat(&[&zero, &vec![0; 128], &g, &vec![0; 128]]));
    pc(s, "neg.g2_not_in_subgroup", cat(&[&g, &bn_g2_not_in_subgroup()]));
    let mut q_off = q.clone();
    q_off[64] ^= 1;
    pc(s, "neg.g2_off_curve", cat(&[&g, &q_off]));
    pc(s, "neg.g2_noncanonical", cat(&[&g, &p_le, &q[32..]]));
    pc(s, "neg.g1_off_curve", cat(&[&off_curve, &q]));
    pc(s, "neg.len191", cat(&[&g, &q[..127]]));
    push(s, "alt_bn128_pairing_check_reg", "pos.register_input", cat(&[&g, &q, &neg_g, &q]), 100);
    push(s, "alt_bn128_pairing_check_oob", "neg.memory_oob", vec![], 100);
    // base 9.686 Tgas, then 2 x 5.102 at the per-element charge > 15 Tgas
    push(s, "alt_bn128_pairing_check", "neg.gas_at_element_charge", cat(&[&g, &q, &neg_g, &q]), 15);
}

// ---------------------------------------------------------------------------------------------
// BLS12-381

const BLS_P: &str = "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab";
const BLS_R: &str = "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001";

fn le_u64(n: u64) -> [u8; 32] {
    let mut o = [0u8; 32];
    o[..8].copy_from_slice(&n.to_le_bytes());
    o
}
fn fp(be: &[u8]) -> blst::blst_fp {
    let mut b = [0u8; 48];
    b[48 - be.len()..].copy_from_slice(be);
    let mut f = blst::blst_fp::default();
    unsafe { blst::blst_fp_from_bendian(&mut f, b.as_ptr()) };
    f
}
fn fp_n(n: u64) -> blst::blst_fp {
    fp(&n.to_be_bytes())
}
fn fp_be(f: &blst::blst_fp) -> [u8; 48] {
    let mut b = [0u8; 48];
    unsafe { blst::blst_bendian_from_fp(b.as_mut_ptr(), f) };
    b
}
/// a canonical Fp element derived from a tag (< 2^256 < p)
fn fp_tag(tag: &str) -> [u8; 48] {
    let mut b = [0u8; 48];
    b[16..].copy_from_slice(&digest(tag));
    b
}

macro_rules! bls_group {
    ($m:ident, $p:ident, $aff:ident, $gen:ident, $mult:ident, $cneg:ident, $ser:ident, $comp:ident,
     $aser:ident, $acomp:ident, $on:ident, $ing:ident, $n:expr) => {
        mod $m {
            pub const N: usize = $n;
            pub fn mul(k: u64) -> blst::$p {
                let s = super::le_u64(k);
                let mut o = blst::$p::default();
                unsafe { blst::$mult(&mut o, blst::$gen(), s.as_ptr(), 64) };
                o
            }
            pub fn neg(mut p: blst::$p) -> blst::$p {
                unsafe { blst::$cneg(&mut p, true) };
                p
            }
            pub fn ser(p: &blst::$p) -> Vec<u8> {
                let mut b = [0u8; 2 * N];
                unsafe { blst::$ser(b.as_mut_ptr(), p) };
                b.to_vec()
            }
            pub fn comp(p: &blst::$p) -> Vec<u8> {
                let mut b = [0u8; N];
                unsafe { blst::$comp(b.as_mut_ptr(), p) };
                b.to_vec()
            }
            pub fn aser(p: &blst::$aff) -> Vec<u8> {
                let mut b = [0u8; 2 * N];
                unsafe { blst::$aser(b.as_mut_ptr(), p) };
                b.to_vec()
            }
            pub fn acomp(p: &blst::$aff) -> Vec<u8> {
                let mut b = [0u8; N];
                unsafe { blst::$acomp(b.as_mut_ptr(), p) };
                b.to_vec()
            }
            pub fn on_curve(p: &blst::$aff) -> bool {
                unsafe { blst::$on(p) }
            }
            pub fn in_group(p: &blst::$aff) -> bool {
                unsafe { blst::$ing(p) }
            }
            pub fn infinity() -> Vec<u8> {
                let mut b = vec![0u8; 2 * N];
                b[0] = 0x40;
                b
            }
            pub fn infinity_comp() -> Vec<u8> {
                let mut b = vec![0u8; N];
                b[0] = 0xc0;
                b
            }
        }
    };
}
bls_group!(g1, blst_p1, blst_p1_affine, blst_p1_generator, blst_p1_mult, blst_p1_cneg, blst_p1_serialize,
    blst_p1_compress, blst_p1_affine_serialize, blst_p1_affine_compress, blst_p1_affine_on_curve,
    blst_p1_affine_in_g1, 48);
bls_group!(g2, blst_p2, blst_p2_affine, blst_p2_generator, blst_p2_mult, blst_p2_cneg, blst_p2_serialize,
    blst_p2_compress, blst_p2_affine_serialize, blst_p2_affine_compress, blst_p2_affine_on_curve,
    blst_p2_affine_in_g2, 96);

fn fp_cube_plus(x: &blst::blst_fp, b: &blst::blst_fp) -> blst::blst_fp {
    let mut t = blst::blst_fp::default();
    let mut r = blst::blst_fp::default();
    unsafe {
        blst::blst_fp_sqr(&mut t, x);
        blst::blst_fp_mul(&mut t, &t, x);
        blst::blst_fp_add(&mut r, &t, b);
    }
    r
}
fn fp2_cube_plus(x: &blst::blst_fp2, b: &blst::blst_fp2) -> blst::blst_fp2 {
    let mut t = blst::blst_fp2::default();
    let mut r = blst::blst_fp2::default();
    unsafe {
        blst::blst_fp2_sqr(&mut t, x);
        blst::blst_fp2_mul(&mut t, &t, x);
        blst::blst_fp2_add(&mut r, &t, b);
    }
    r
}
/// (on-curve, not in G1) affine point, and an x for which x^3 + 4 is not a square
fn bls_g1_specials() -> (blst::blst_p1_affine, [u8; 48]) {
    let four = fp_n(4);
    let (mut pt, mut bad_x) = (None, None);
    for k in 1u64.. {
        let x = fp_n(k);
        let rhs = fp_cube_plus(&x, &four);
        let mut y = blst::blst_fp::default();
        if unsafe { blst::blst_fp_sqrt(&mut y, &rhs) } {
            let a = blst::blst_p1_affine { x, y };
            if pt.is_none() && g1::on_curve(&a) && !g1::in_group(&a) {
                pt = Some(a);
            }
        } else if bad_x.is_none() {
            bad_x = Some(fp_be(&x));
        }
        if let (Some(p), Some(b)) = (pt, bad_x) {
            return (p, b);
        }
    }
    unreachable!()
}
fn bls_g2_specials() -> (blst::blst_p2_affine, [u8; 96]) {
    let b = blst::blst_fp2 { fp: [fp_n(4), fp_n(4)] };
    let (mut pt, mut bad_x) = (None, None);
    for k in 1u64.. {
        let x = blst::blst_fp2 { fp: [fp_n(k), fp_n(1)] };
        let rhs = fp2_cube_plus(&x, &b);
        let mut y = blst::blst_fp2::default();
        if unsafe { blst::blst_fp2_sqrt(&mut y, &rhs) } {
            let a = blst::blst_p2_affine { x, y };
            if pt.is_none() && g2::on_curve(&a) && !g2::in_group(&a) {
                pt = Some(a);
            }
        } else if bad_x.is_none() {
            // Fp2 encoding c1 ‖ c0
            let mut e = [0u8; 96];
            e[..48].copy_from_slice(&fp_be(&x.fp[1]));
            e[48..].copy_from_slice(&fp_be(&x.fp[0]));
            bad_x = Some(e);
        }
        if let (Some(p), Some(bx)) = (pt, bad_x) {
            return (p, bx);
        }
    }
    unreachable!()
}

fn bls(s: &mut Vec<Step>) {
    let p = hex48(BLS_P);
    let r_le = hex32_be_to_le(BLS_R);
    let (g1_ns, g1_bad_x) = bls_g1_specials();
    let (g2_ns, g2_bad_x) = bls_g2_specials();

    // ---- G1 encodings
    let a = g1::ser(&g1::mul(1));
    let a2 = g1::ser(&g1::mul(2));
    let a_neg = g1::ser(&g1::neg(g1::mul(1)));
    let a_ns = g1::aser(&g1_ns);
    let a_off = cat(&[&fp_be(&fp_n(1)), &fp_be(&fp_n(1))]);
    let a_x_is_p = cat(&[&p, &a[48..]]);
    let a_x_plus_p = cat(&[&add_be(&a[..48], &p), &a[48..]]);
    let a_corner = cat(&[&[0u8; 48], &fp_be(&fp_n(2))]); // (0, 2): on the curve, order 3
    let mut a_flagged = a.clone();
    a_flagged[0] |= 0x80;
    let mut a_inf_dirty = g1::infinity();
    a_inf_dirty[95] = 1;

    let p1sum = |s: &mut Vec<Step>, case: &str, args: Vec<u8>| push(s, "bls12381_p1_sum", case, args, 100);
    p1sum(s, "pos.empty", vec![]);
    p1sum(s, "pos.a+2a-a", cat(&[&[0], &a, &[0], &a2, &[1], &a]));
    p1sum(s, "pos.infinity", cat(&[&[0], &g1::infinity(), &[1], &g1::infinity()]));
    p1sum(s, "pos.a+neg_a", cat(&[&[0], &a, &[0], &a_neg]));
    p1sum(s, "edge.not_in_subgroup", cat(&[&[0], &a_ns, &[0], &a]));
    p1sum(s, "edge.corner_0_2", cat(&[&[0], &a_corner]));
    p1sum(s, "neg.sign2", cat(&[&[2], &a]));
    p1sum(s, "neg.off_curve", cat(&[&[0], &a_off]));
    p1sum(s, "neg.x_is_p", cat(&[&[0], &a_x_is_p]));
    p1sum(s, "neg.x_plus_p", cat(&[&[0], &a_x_plus_p]));
    p1sum(s, "neg.compression_flag", cat(&[&[0], &a_flagged]));
    p1sum(s, "neg.infinity_nonzero", cat(&[&[0], &a_inf_dirty]));
    p1sum(s, "neg.len96", a.clone());
    push(s, "bls12381_p1_sum_reg", "neg.register_input", cat(&[&[0], &a]), 100);
    push(s, "bls12381_p1_sum_oob", "neg.memory_oob", vec![], 100);

    let mexp1 = |s: &mut Vec<Step>, case: &str, args: Vec<u8>, tg| push(s, "bls12381_g1_multiexp", case, args, tg);
    mexp1(s, "pos.empty", vec![], 100);
    mexp1(s, "pos.5a+7(2a)", cat(&[&a, &le_u64(5), &a2, &le_u64(7)]), 100);
    mexp1(s, "pos.scalar0", cat(&[&a, &[0; 32]]), 100);
    mexp1(s, "edge.scalar_r", cat(&[&a, &r_le]), 100);
    mexp1(s, "edge.scalar_max", cat(&[&a2, &[0xff; 32]]), 100);
    mexp1(s, "pos.infinity", cat(&[&g1::infinity(), &le_u64(3)]), 100);
    mexp1(s, "neg.not_in_subgroup", cat(&[&a_ns, &le_u64(3)]), 100);
    mexp1(s, "neg.off_curve", cat(&[&a_off, &le_u64(3)]), 100);
    mexp1(s, "neg.x_is_p", cat(&[&a_x_is_p, &le_u64(3)]), 100);
    mexp1(s, "neg.len127", cat(&[&a, &[1; 31]]), 100);
    // base 0.0165 + 3 x 0.93 Tgas > 2 Tgas at the per-element charge (before the read)
    mexp1(s, "neg.gas_at_element_charge", cat(&[&a, &le_u64(2), &a, &le_u64(3), &a, &le_u64(4)]), 2);

    let dec1 = |s: &mut Vec<Step>, case: &str, args: Vec<u8>| push(s, "bls12381_p1_decompress", case, args, 100);
    let c = g1::comp(&g1::mul(1));
    let mut c_noflag = c.clone();
    c_noflag[0] &= 0x7f;
    let mut c_inf_and_point = c.clone();
    c_inf_and_point[0] |= 0x40;
    let mut c_bad_x = g1_bad_x.to_vec();
    c_bad_x[0] |= 0x80;
    let mut c_x_is_p = p.to_vec();
    c_x_is_p[0] |= 0x80;
    let mut c_corner = vec![0u8; 48];
    c_corner[0] = 0x80;
    dec1(s, "pos.empty", vec![]);
    dec1(s, "pos.a", c.clone());
    dec1(s, "pos.2a,neg_a,inf", cat(&[&g1::comp(&g1::mul(2)), &g1::comp(&g1::neg(g1::mul(1))), &g1::infinity_comp()]));
    dec1(s, "edge.not_in_subgroup", g1::acomp(&g1_ns));
    dec1(s, "neg.no_compression_flag", c_noflag);
    dec1(s, "neg.infinity_and_point", c_inf_and_point);
    dec1(s, "neg.x_not_on_curve", c_bad_x);
    dec1(s, "neg.x_is_p", c_x_is_p);
    dec1(s, "edge.corner_0_2", c_corner);
    dec1(s, "neg.len47", c[..47].to_vec());

    let map1 = |s: &mut Vec<Step>, case: &str, args: Vec<u8>| push(s, "bls12381_map_fp_to_g1", case, args, 100);
    map1(s, "pos.empty", vec![]);
    map1(s, "pos.one", fp_tag("map-fp-0").to_vec());
    map1(s, "pos.three", cat(&[&fp_tag("map-fp-1"), &[0u8; 48], &sub_be(&p, &fp_be(&fp_n(1)))]));
    map1(s, "neg.fp_is_p", p.to_vec());
    map1(s, "neg.second_noncanonical", cat(&[&fp_tag("map-fp-2"), &add_be(&fp_tag("map-fp-3"), &p)]));
    map1(s, "neg.len47", fp_tag("map-fp-4")[..47].to_vec());

    // ---- G2 encodings
    let b = g2::ser(&g2::mul(1));
    let b2 = g2::ser(&g2::mul(2));
    let b_neg = g2::ser(&g2::neg(g2::mul(1)));
    let b_ns = g2::aser(&g2_ns);
    let b_off = cat(&[&[0u8; 95], &[1], &[0u8; 95], &[1]]);
    let b_c1_is_p = cat(&[&p, &b[48..]]);
    let b_c0_is_p = cat(&[&b[..48], &p, &b[96..]]);
    let mut b_flagged = b.clone();
    b_flagged[0] |= 0x80;

    let p2sum = |s: &mut Vec<Step>, case: &str, args: Vec<u8>| push(s, "bls12381_p2_sum", case, args, 100);
    p2sum(s, "pos.empty", vec![]);
    p2sum(s, "pos.b+2b-b", cat(&[&[0], &b, &[0], &b2, &[1], &b]));
    p2sum(s, "pos.infinity", cat(&[&[1], &g2::infinity()]));
    p2sum(s, "pos.b+neg_b", cat(&[&[0], &b, &[0], &b_neg]));
    p2sum(s, "edge.not_in_subgroup", cat(&[&[0], &b_ns]));
    p2sum(s, "neg.sign255", cat(&[&[255], &b]));
    p2sum(s, "neg.off_curve", cat(&[&[0], &b_off]));
    p2sum(s, "neg.c1_is_p", cat(&[&[0], &b_c1_is_p]));
    p2sum(s, "neg.c0_is_p", cat(&[&[0], &b_c0_is_p]));
    p2sum(s, "neg.compression_flag", cat(&[&[0], &b_flagged]));
    p2sum(s, "neg.len194", cat(&[&[0], &b, &[0]]));

    let mexp2 = |s: &mut Vec<Step>, case: &str, args: Vec<u8>, tg| push(s, "bls12381_g2_multiexp", case, args, tg);
    mexp2(s, "pos.empty", vec![], 100);
    mexp2(s, "pos.5b+7(2b)", cat(&[&b, &le_u64(5), &b2, &le_u64(7)]), 100);
    mexp2(s, "edge.scalar_r", cat(&[&b, &r_le]), 100);
    mexp2(s, "pos.infinity", cat(&[&g2::infinity(), &le_u64(3)]), 100);
    mexp2(s, "neg.not_in_subgroup", cat(&[&b_ns, &le_u64(3)]), 100);
    mexp2(s, "neg.off_curve", cat(&[&b_off, &le_u64(3)]), 100);
    mexp2(s, "neg.c0_is_p", cat(&[&b_c0_is_p, &le_u64(3)]), 100);
    mexp2(s, "neg.len223", cat(&[&b, &[1; 31]]), 100);
    // base 0.0186 + 3 x 1.995 Tgas > 5 Tgas at the per-element charge
    mexp2(s, "neg.gas_at_element_charge", cat(&[&b, &le_u64(2), &b, &le_u64(3), &b, &le_u64(4)]), 5);

    let dec2 = |s: &mut Vec<Step>, case: &str, args: Vec<u8>| push(s, "bls12381_p2_decompress", case, args, 100);
    let d = g2::comp(&g2::mul(1));
    let mut d_noflag = d.clone();
    d_noflag[0] &= 0x7f;
    let mut d_bad_x = g2_bad_x.to_vec();
    d_bad_x[0] |= 0x80;
    let mut d_c1_is_p = cat(&[&p, &d[48..]]);
    d_c1_is_p[0] |= 0x80;
    dec2(s, "pos.empty", vec![]);
    dec2(s, "pos.b", d.clone());
    dec2(s, "pos.2b,neg_b,inf", cat(&[&g2::comp(&g2::mul(2)), &g2::comp(&g2::neg(g2::mul(1))), &g2::infinity_comp()]));
    dec2(s, "edge.not_in_subgroup", g2::acomp(&g2_ns));
    dec2(s, "neg.no_compression_flag", d_noflag);
    dec2(s, "neg.x_not_on_curve", d_bad_x);
    dec2(s, "neg.c1_is_p", d_c1_is_p);
    dec2(s, "neg.len95", d[..95].to_vec());

    let map2 = |s: &mut Vec<Step>, case: &str, args: Vec<u8>| push(s, "bls12381_map_fp2_to_g2", case, args, 100);
    map2(s, "pos.empty", vec![]);
    map2(s, "pos.one", cat(&[&fp_tag("map-fp2-c1"), &fp_tag("map-fp2-c0")]));
    map2(s, "pos.two", cat(&[&[0u8; 96], &sub_be(&p, &fp_be(&fp_n(1))), &fp_tag("map-fp2-x")]));
    map2(s, "neg.c1_is_p", cat(&[&p, &fp_tag("map-fp2-c0")]));
    map2(s, "neg.c0_is_p", cat(&[&fp_tag("map-fp2-c1"), &p]));
    map2(s, "neg.len95", vec![0; 95]);

    // ---- pairing: [(p1 96 B, p2 192 B)]
    let pc = |s: &mut Vec<Step>, case: &str, args: Vec<u8>, tg| push(s, "bls12381_pairing_check", case, args, tg);
    let a5 = g1::ser(&g1::mul(5));
    let b5 = g2::ser(&g2::mul(5));
    pc(s, "pos.empty", vec![], 100);
    pc(s, "pos.e(5a,b)e(-a,5b)", cat(&[&a5, &b, &a_neg, &b5]), 100);
    pc(s, "pos.e(a,b)", cat(&[&a, &b]), 100);
    pc(s, "pos.infinity_pairs", cat(&[&g1::infinity(), &b, &a, &g2::infinity()]), 100);
    pc(s, "neg.g1_not_in_subgroup", cat(&[&a_ns, &b]), 100);
    pc(s, "neg.g2_not_in_subgroup", cat(&[&a, &b_ns]), 100);
    pc(s, "neg.g1_off_curve", cat(&[&a_off, &b]), 100);
    pc(s, "neg.g2_compression_flag", cat(&[&a, &b_flagged]), 100);
    pc(s, "neg.g1_x_is_p", cat(&[&a_x_is_p, &b]), 100);
    pc(s, "neg.len287", cat(&[&a, &b[..191]]), 100);
    push(s, "bls12381_pairing_check_reg", "pos.register_input", cat(&[&a5, &b, &a_neg, &b5]), 100);
    push(s, "bls12381_pairing_check_oob", "neg.memory_oob", vec![], 100);
    // base 2.13 Tgas, read, then 2 x 2.13 at the per-element charge > 5 Tgas
    pc(s, "neg.gas_at_element_charge", cat(&[&a5, &b, &a_neg, &b5]), 5);
}

// ---------------------------------------------------------------------------------------------
// p256_verify, ecrecover

const P256_N: &str = "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551";

fn p256(s: &mut Vec<Step>) {
    use p256::ecdsa::signature::hazmat::PrehashSigner;
    use p256::ecdsa::{Signature, SigningKey, VerifyingKey};
    let sk = SigningKey::from_slice(&digest("curve-hosts p256 key")).unwrap();
    let pk_c = VerifyingKey::from(&sk).to_encoded_point(true).as_bytes().to_vec();
    let pk_u = VerifyingKey::from(&sk).to_encoded_point(false).as_bytes().to_vec();
    let h = digest("curve-hosts p256 message");
    let sig: Signature = sk.sign_prehash(&h).unwrap();
    let sig = sig.to_bytes().to_vec();
    let n = hex::decode(P256_N).unwrap();
    let high_s = cat(&[&sig[..32], &sub_be(&n, &sig[32..])]);
    let args = |sig: &[u8], pk: &[u8], msg: &[u8]| cat(&[&[sig.len() as u8, pk.len() as u8], sig, pk, msg]);
    let v = |s: &mut Vec<Step>, case: &str, a: Vec<u8>| push(s, "p256_verify", case, a, 100);
    v(s, "pos.valid", args(&sig, &pk_c, &h));
    v(s, "pos.high_s", args(&high_s, &pk_c, &h));
    v(s, "neg.wrong_message", args(&sig, &pk_c, &digest("other message")));
    let mut pk_other_parity = pk_c.clone();
    pk_other_parity[0] ^= 1;
    v(s, "neg.other_parity_key", args(&sig, &pk_other_parity, &h));
    v(s, "neg.r_zero", args(&cat(&[&[0; 32], &sig[32..]]), &pk_c, &h));
    v(s, "neg.s_is_n", args(&cat(&[&sig[..32], &n]), &pk_c, &h));
    let mut pk_bad_prefix = pk_c.clone();
    pk_bad_prefix[0] = 0x04;
    v(s, "neg.key_prefix_04", args(&sig, &pk_bad_prefix, &h));
    v(s, "neg.key_x_ff", args(&sig, &cat(&[&[0x02], &[0xff; 32]]), &h));
    v(s, "edge.empty_message", args(&sig, &pk_c, &[]));
    v(s, "edge.long_message", args(&sig, &pk_c, &cat(&[&h, &h])));
    v(s, "neg.sig_len63", args(&sig[..63], &pk_c, &h));
    v(s, "neg.key_uncompressed65", args(&sig, &pk_u, &h));
    v(s, "neg.key_len32", args(&sig, &pk_c[..32], &h));
}

fn ecrecover(s: &mut Vec<Step>) {
    use near_crypto::{KeyType, SecretKey};
    let sk = SecretKey::from_seed(KeyType::SECP256K1, "curve-hosts secp256k1 key");
    let h = digest("curve-hosts ecrecover message");
    let raw = borsh::to_vec(&sk.sign(&h)).unwrap();
    assert_eq!(raw.len(), 66);
    let (sig, v) = (raw[1..65].to_vec(), raw[65]);
    let args = |v: u8, flag: u8, sig: &[u8], hash: &[u8]| cat(&[&[v, flag, sig.len() as u8, hash.len() as u8], sig, hash]);
    let e = |s: &mut Vec<Step>, case: &str, a: Vec<u8>| push(s, "ecrecover", case, a, 100);
    e(s, "pos.valid", args(v, 0, &sig, &h));
    e(s, "pos.valid_flag1", args(v, 1, &sig, &h));
    e(s, "neg.wrong_v", args(v ^ 1, 0, &sig, &h));
    e(s, "neg.r_zero", args(v, 0, &cat(&[&[0; 32], &sig[32..]]), &h));
    e(s, "neg.v4", args(4, 0, &sig, &h));
    e(s, "neg.flag2", args(v, 2, &sig, &h));
    e(s, "neg.sig_len63", args(v, 0, &sig[..63], &h));
    e(s, "neg.hash_len31", args(v, 0, &sig, &h[..31]));
}

fn push(s: &mut Vec<Step>, method: &'static str, case: &str, args: Vec<u8>, tgas: u64) {
    let host = method.trim_end_matches("_reg").trim_end_matches("_oob");
    let label = format!("successor.curve-hosts.{:03}.{host}.{case}", s.len());
    s.push(Step { label, method, args, tgas });
}

fn build() -> Vec<Step> {
    let mut s = Vec::new();
    alt_bn128(&mut s);
    bls(&mut s);
    p256(&mut s);
    ecrecover(&mut s);
    let mut keys = std::collections::HashSet::new();
    for x in &s {
        assert!(keys.insert((x.method, x.args.clone(), x.tgas)), "duplicate step key: {}", x.label);
    }
    s
}

/// `curve-steps`: the scenario as JSON, for collectors (a step is identified in a chunk by its
/// method, args hash and attached gas, which `build` keeps unique).
pub fn print_steps() -> i32 {
    use sha2::Digest;
    let rows: Vec<serde_json::Value> = steps()
        .iter()
        .map(|s| {
            serde_json::json!({
                "label": s.label, "method": s.method, "args_hex": hex::encode(&s.args),
                "args_sha256": hex::encode(sha2::Sha256::digest(&s.args)),
                "gas": near_primitives::types::Gas::from_teragas(s.tgas).as_gas(),
            })
        })
        .collect();
    let out = serde_json::json!({
        "contract_sha256": hex::encode(sha2::Sha256::digest(code())),
        "contract_hash": near_primitives::hash::CryptoHash::hash_bytes(code()).to_string(),
        "contract_len": code().len(),
        "accounts": [ACCOUNT_A, ACCOUNT_B],
        "steps": rows,
    });
    println!("{}", serde_json::to_string_pretty(&out).unwrap());
    0
}
