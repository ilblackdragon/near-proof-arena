//! Field `F = BabyBear` (p = 15·2^27 + 1) and challenge field
//! `K = F[X]/(X^8 - 11)` (Plonky3's `BinomialExtensionField<BabyBear, 8>`),
//! plus the canonical byte encodings used on the wire and inside hashes.
//!
//! Encodings (all little-endian):
//! * `F`: 4 bytes, canonical `u32` in `[0, p)`.
//! * `K`: 32 bytes, the 8 coefficients of `1, X, …, X^7`, each as `F`.

use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};

pub type F = BabyBear;
pub type EF = BinomialExtensionField<BabyBear, 8>;

pub const P: u32 = 0x7800_0001;
/// Multiplicative generator of `F^*`; the LDE coset shift base `s`.
pub const SHIFT: u32 = 31;
pub const EXT_DEG: usize = 8;

#[inline]
pub fn f(x: u32) -> F {
    F::new(x)
}

#[inline]
pub fn shift() -> F {
    F::new(SHIFT)
}

/// Canonical generator of the subgroup of order `2^log` (Plonky3's
/// `two_adic_generator`, i.e. `0x1a427a41^(2^(27-log))`).
#[inline]
pub fn omega(log: usize) -> F {
    F::two_adic_generator(log)
}

#[inline]
pub fn put_f(out: &mut Vec<u8>, x: F) {
    out.extend_from_slice(&x.as_canonical_u32().to_le_bytes());
}

#[inline]
pub fn put_ef(out: &mut Vec<u8>, x: EF) {
    for c in x.as_basis_coefficients_slice() {
        put_f(out, *c);
    }
}

#[inline]
pub fn ef_coeffs(x: &EF) -> &[F] {
    x.as_basis_coefficients_slice()
}

#[inline]
pub fn ef_from_coeffs(c: &[F]) -> EF {
    EF::from_basis_coefficients_fn(|i| c[i])
}

#[inline]
pub fn ef_from_base(x: F) -> EF {
    EF::from(x)
}

/// Is `x` in the base field (all non-constant coefficients zero)?
pub fn ef_is_base(x: &EF) -> bool {
    ef_coeffs(x)[1..].iter().all(|c| c.is_zero())
}

/// Read a canonical `F` (rejects non-canonical encodings).
pub fn read_f(b: &[u8]) -> Option<F> {
    let v = u32::from_le_bytes(b.try_into().ok()?);
    if v < P { Some(F::new(v)) } else { None }
}

pub fn read_ef(b: &[u8]) -> Option<EF> {
    if b.len() != 32 {
        return None;
    }
    let mut c = [F::ZERO; 8];
    for i in 0..8 {
        c[i] = read_f(&b[4 * i..4 * i + 4])?;
    }
    Some(ef_from_coeffs(&c))
}

/// `decodeChal`: 8 big-endian u32 limbs, each reduced mod p, limb i is the
/// coefficient of `X^i`.
pub fn decode_chal(y: &[u8; 32]) -> EF {
    let mut c = [F::ZERO; 8];
    for i in 0..8 {
        let v = u32::from_be_bytes(y[4 * i..4 * i + 4].try_into().unwrap());
        c[i] = F::new(v % P);
    }
    ef_from_coeffs(&c)
}

/// `decodeOod`: `decodeChal`, then if limbs 1..7 are all zero, limb 1 := 1,
/// so the result lies in `K \ F`.
pub fn decode_ood(y: &[u8; 32]) -> EF {
    let x = decode_chal(y);
    if ef_is_base(&x) {
        let mut c = [F::ZERO; 8];
        c.copy_from_slice(ef_coeffs(&x));
        c[1] = F::ONE;
        ef_from_coeffs(&c)
    } else {
        x
    }
}

pub fn inv_f(x: F) -> F {
    x.inverse()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constants() {
        assert_eq!(omega(27).as_canonical_u32(), 0x1a42_7a41);
        assert_eq!(omega(27).exp_power_of_2(27), F::ONE);
        assert_ne!(omega(27).exp_power_of_2(26), F::ONE);
        assert_eq!(omega(3), omega(4).square());
        // X^8 = 11
        let x = ef_from_coeffs(&[
            F::ZERO,
            F::ONE,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
        ]);
        assert_eq!(x.exp_u64(8), ef_from_base(F::new(11)));
    }
}
