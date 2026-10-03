//! SHA-256 compression constraints, vendored verbatim (function bodies) from
//! Plonky3 `sha256-air/src/air.rs` at rev 3acc8b70e68d6c2afc03930700c26540bd47458d
//! (MIT OR Apache-2.0). Only change: the five phases are exposed through
//! [`eval_sha_row`] so that the arena's SHA table can embed the compression
//! columns as a prefix of a wider row.

use p3_air::utils::pack_bits_le;
use p3_air::AirBuilder;
use p3_field::integers::QuotientMap;
use p3_field::{Dup, PrimeCharacteristicRing};
use p3_sha256_air::{
    BITS_PER_LIMB, BLOCK_WORDS, CHAIN_LEN, SCHEDULE_EXTENSIONS, SHA256_K, Sha256Cols,
    U32_LIMBS, WORD_BITS,
};

/// All constraints of one compression (degree <= 3).
pub fn eval_sha_row<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::Var>) {
    eval_bit_range_checks::<AB>(builder, local);
    eval_initial_state::<AB>(builder, local);
    eval_message_schedule::<AB>(builder, local);
    eval_compression::<AB>(builder, local);
    eval_finalization::<AB>(builder, local);
}

/// Emit `b * (b - 1) = 0` for every bit-valued column in the row.
///
/// Required because downstream XOR and AND identities only produce correct
/// results when their inputs are strictly `{0, 1}`.
fn eval_bit_range_checks<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::Var>) {
    // Range-check every message-schedule word, including the 16 block words
    // supplied as pure witness and the 48 expanded words.
    for word in &local.w {
        builder.assert_bools(*word);
    }

    // Range-check the `a` chain.
    // - Indices 0..4 cover the input state bits;
    // - Indices 4..68 cover every `new_a` produced by the compression loop.
    for word in &local.a_chain {
        builder.assert_bools(*word);
    }
    // Symmetric range check for the `e` chain.
    for word in &local.e_chain {
        builder.assert_bools(*word);
    }

    // Range-check the output chaining state.
    //
    // Invariant: nothing downstream re-derives `h_out`.
    // These booleans are the only thing bounding its two limbs by `2^16`.
    for word in &local.h_out {
        builder.assert_bools(*word);
    }
}

/// Assert that each packed `H[i]` agrees with the matching chain entry.
///
/// Layout mirrored from the columns module:
///
/// ```text
///     H_0 <-> a_chain[3]   H_4 <-> e_chain[3]
///     H_1 <-> a_chain[2]   H_5 <-> e_chain[2]
///     H_2 <-> a_chain[1]   H_6 <-> e_chain[1]
///     H_3 <-> a_chain[0]   H_7 <-> e_chain[0]
/// ```
fn eval_initial_state<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::Var>) {
    // Words H_0..H_3 live in the reversed prefix of the `a` chain.
    for i in 0..4 {
        // The chain stores (d, c, b, a) at indices (0, 1, 2, 3), so invert.
        let chain_idx = 3 - i;
        let bits = &local.a_chain[chain_idx];
        assert_packed_equals_bits::<AB>(builder, &local.h_in[i], bits);
    }
    // Words H_4..H_7 live in the reversed prefix of the `e` chain.
    for i in 0..4 {
        let chain_idx = 3 - i;
        let bits = &local.e_chain[chain_idx];
        assert_packed_equals_bits::<AB>(builder, &local.h_in[4 + i], bits);
    }
}

/// Enforce the 48 new message-schedule words.
///
/// For every `t` in `[16, 64)`:
///
/// ```text
///     small_sigma0 = ROTR_7 (W[t - 15]) XOR ROTR_18(W[t - 15]) XOR SHR_3 (W[t - 15])
///     small_sigma1 = ROTR_17(W[t - 2 ]) XOR ROTR_19(W[t - 2 ]) XOR SHR_10(W[t - 2 ])
///     tmp          = small_sigma1 + W[t - 7]                   (mod 2^32)
///     W[t]         = tmp + small_sigma0 + W[t - 16]            (mod 2^32)
/// ```
///
/// The four-term sum is split into two three-term sums because the shared
/// add helpers saturate at three addends.
fn eval_message_schedule<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::Var>) {
    // Loop over the 48 expanded schedule positions. `i` indexes the packed
    // auxiliary columns; `t` indexes into the unpacked `w` array.
    for i in 0..SCHEDULE_EXTENSIONS {
        let t = i + BLOCK_WORDS;

        // Bind small_sigma0 to the packed column via per-bit XOR-3 expansion.
        assert_sigma_matches::<AB>(
            builder,
            &local.w[t - 15],
            SigmaSpec::SmallSigma0,
            &local.sched_sigma0[i],
        );

        // Bind small_sigma1 to the packed column via per-bit XOR-3 expansion.
        assert_sigma_matches::<AB>(
            builder,
            &local.w[t - 2],
            SigmaSpec::SmallSigma1,
            &local.sched_sigma1[i],
        );

        // Three-term add #1: tmp = small_sigma1 + W[t - 7].
        //
        // W[t - 7] is consumed as an expression packed on the fly from its
        // bit decomposition - no extra column is needed for it.
        let w_tm7_packed_expr = pack_word::<AB>(&local.w[t - 7]);
        add2(
            builder,
            &local.sched_tmp[i],
            &local.sched_sigma1[i],
            &w_tm7_packed_expr,
        );

        // Three-term add #2: pack(W[t]) = tmp + small_sigma_0 + W[t - 16].
        //
        // Output slot is an expression, not a committed column — `W[t]` is
        // already boolean-checked bit-wise, so its packing is free.
        let w_t_packed_expr = pack_word::<AB>(&local.w[t]);
        let sched_sigma0_expr: [AB::Expr; U32_LIMBS] = local.sched_sigma0[i].map(Into::into);
        let w_tm16_packed_expr = pack_word::<AB>(&local.w[t - 16]);
        add3_expr_out(
            builder,
            &w_t_packed_expr,
            &local.sched_tmp[i],
            &sched_sigma0_expr,
            &w_tm16_packed_expr,
        );
    }
}

/// Enforce one compression round per iteration.
///
/// Each round reads its eight working variables from the chains and
/// evaluates:
///
/// ```text
///     big_sigma1 = ROTR_6 (e) XOR ROTR_11(e) XOR ROTR_25(e)
///     ch         = (e AND f) XOR (NOT e AND g)
///     tmp1       = h + big_sigma1 + ch               (mod 2^32)
///     T1         = tmp1 + K[t] + W[t]                (mod 2^32)
///     big_sigma0 = ROTR_2 (a) XOR ROTR_13(a) XOR ROTR_22(a)
///     maj        = (a AND b) XOR (a AND c) XOR (b AND c)
///     new_a      = T1 + big_sigma0 + maj             (mod 2^32)
///     new_e      = d  + T1                           (mod 2^32)
/// ```
///
/// # Why one add for `new_a`?
///
/// The spec writes this as two steps:
///
/// ```text
///     T_2   = big_sigma0 + maj
///     new_a = T_1 + T_2
/// ```
///
/// We fuse them into a single three-term add.
///
/// - Drops the `T_2` column.
/// - Constraint degree stays at 3.
fn eval_compression<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::Var>) {
    for (t, round) in local.rounds.iter().enumerate() {
        // Read the eight working variables for round `t` from the chains.
        //
        //     chain[t + 3]  -->  slot a (or e)
        //     chain[t + 2]  -->  slot b (or f)
        //     chain[t + 1]  -->  slot c (or g)
        //     chain[t + 0]  -->  slot d (or h)
        let a_bits = &local.a_chain[t + 3];
        let b_bits = &local.a_chain[t + 2];
        let c_bits = &local.a_chain[t + 1];
        let d_bits = &local.a_chain[t];
        let e_bits = &local.e_chain[t + 3];
        let f_bits = &local.e_chain[t + 2];
        let g_bits = &local.e_chain[t + 1];
        let h_bits = &local.e_chain[t];

        // big_sigma1 check: reduces to a per-bit XOR3 of rotated `e` bits.
        assert_sigma_matches::<AB>(builder, e_bits, SigmaSpec::BigSigma1, &round.sigma1_e);

        // Ch check: disjoint AND-terms collapse the XOR to an addition.
        //
        //     Ch_i = e_i * f_i + (1 - e_i) * g_i
        assert_ch_matches::<AB>(builder, e_bits, f_bits, g_bits, &round.ch);

        // Three-term add: tmp1 = big_sigma1 + ch + h.
        let ch_expr: [AB::Expr; U32_LIMBS] = round.ch.map(Into::into);
        let h_packed_expr = pack_word::<AB>(h_bits);
        add3(
            builder,
            &round.tmp1,
            &round.sigma1_e,
            &ch_expr,
            &h_packed_expr,
        );

        // Inject K[t] as a constant expression, one 16-bit limb at a time.
        let k_expr: [AB::Expr; U32_LIMBS] = [
            // Low 16 bits of K[t].
            AB::Expr::from_u32(SHA256_K[t] & 0xFFFF),
            // High 16 bits of K[t].
            AB::Expr::from_u32(SHA256_K[t] >> BITS_PER_LIMB),
        ];
        // Three-term add: T1 = tmp1 + K[t] + W[t].
        let w_packed_expr = pack_word::<AB>(&local.w[t]);
        add3(builder, &round.t1, &round.tmp1, &k_expr, &w_packed_expr);

        // big_sigma0 check: per-bit XOR3 of rotated `a` bits.
        assert_sigma_matches::<AB>(builder, a_bits, SigmaSpec::BigSigma0, &round.sigma0_a);

        // Maj check: degree-3 identity `a * b + c * (a XOR b)`.
        assert_maj_matches::<AB>(builder, a_bits, b_bits, c_bits, &round.maj);

        // Three-term add straight into the next `a`-chain slot.
        //
        //     pack(a_chain[t + 4]) = T_1 + big_sigma_0 + maj
        //
        // Fuses the spec's two-step update into one add (see the header doc).
        // Output limbs are in `[0, 2^16)` because the chain slot is already
        // boolean-checked.
        let new_a_packed_expr = pack_word::<AB>(&local.a_chain[t + 4]);
        let sigma0_a_expr: [AB::Expr; U32_LIMBS] = round.sigma0_a.map(Into::into);
        let maj_expr: [AB::Expr; U32_LIMBS] = round.maj.map(Into::into);
        add3_expr_out(
            builder,
            &new_a_packed_expr,
            &round.t1,
            &sigma0_a_expr,
            &maj_expr,
        );

        // Two-term add directly into the next `e`-chain slot:
        //     pack(e_chain[t + 4]) = d + T1.
        let new_e_packed_expr = pack_word::<AB>(&local.e_chain[t + 4]);
        let d_packed_expr = pack_word::<AB>(d_bits);
        add2_expr_out(builder, &new_e_packed_expr, &round.t1, &d_packed_expr);
    }
}

/// Enforce `H_out[i] = H_in[i] + final_state[i] (mod 2^32)`.
///
/// The final working variables sit at the tail of the two chains:
///
/// ```text
///     final a = a_chain[67]    final e = e_chain[67]
///     final b = a_chain[66]    final f = e_chain[66]
///     final c = a_chain[65]    final g = e_chain[65]
///     final d = a_chain[64]    final h = e_chain[64]
/// ```
///
/// # Soundness
///
/// The add helpers pin exactly two facts about their output word:
///
/// ```text
///     acc    = out    - in_0    - in_1       in {0, -2^32}
///     acc_16 = out[0] - in_0[0] - in_1[0]    in {0, -2^16}
/// ```
///
/// Neither rules out moving `2^16` from the low limb into the high one:
///
/// ```text
///     out[0] -= 2^16   ->   acc_16 shifts by -2^16
///     out[1] += 1      ->   acc    unchanged
/// ```
///
/// Both checks still hold whenever the honest low-limb carry is `0`.
///
/// So the helper alone admits two limb decompositions per output word.
///
/// One of them puts a limb outside `[0, 2^16)`.
///
/// For an intermediate such as `t1` the alias is harmless:
///
/// - Its consumer's output is repacked from boolean-checked bits.
/// - That consumer's `acc_16` check pins its own low limb modulo `2^16`.
/// - The alias shifts by a multiple of `2^16`, so it cancels there.
///
/// `h_out` has no consumer.
///
/// Committing it as bits makes both limbs 16-bit by construction.
fn eval_finalization<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::Var>) {
    // H'_0..H'_3 are obtained by adding H[i] and the tail of the `a` chain.
    for i in 0..4 {
        let final_bits = &local.a_chain[CHAIN_LEN - 1 - i];
        let packed_expr = pack_word::<AB>(final_bits);
        let h_out_expr = pack_word::<AB>(&local.h_out[i]);
        add2_expr_out(builder, &h_out_expr, &local.h_in[i], &packed_expr);
    }
    // H'_4..H'_7 are obtained by adding H[i] and the tail of the `e` chain.
    for i in 0..4 {
        let final_bits = &local.e_chain[CHAIN_LEN - 1 - i];
        let packed_expr = pack_word::<AB>(final_bits);
        let h_out_expr = pack_word::<AB>(&local.h_out[4 + i]);
        add2_expr_out(builder, &h_out_expr, &local.h_in[4 + i], &packed_expr);
    }
}

/// Pack a 32-bit word of boolean-valued columns into a 2-limb expression.
///
/// # Arguments
///
/// - `bits`: 32 boolean columns in little-endian order.
///
/// # Returns
///
/// A two-element array `[lo_expr, hi_expr]` where:
/// - `lo_expr` equals `sum_{i=0}^{15} 2^i * bits[i]`.
/// - `hi_expr` equals `sum_{i=0}^{15} 2^i * bits[16 + i]`.
#[inline]
fn pack_word<AB: AirBuilder>(bits: &[AB::Var; WORD_BITS]) -> [AB::Expr; U32_LIMBS] {
    [
        // Low limb: bits 0..16.
        pack_bits_le::<AB::Expr, _, _>(bits[..BITS_PER_LIMB].iter().copied()),
        // High limb: bits 16..32.
        pack_bits_le::<AB::Expr, _, _>(bits[BITS_PER_LIMB..].iter().copied()),
    ]
}

/// Assert `packed` equals the packing of `bits`.
///
/// Bridges the packed and unpacked views of a single 32-bit word.
#[inline]
fn assert_packed_equals_bits<AB: AirBuilder>(
    builder: &mut AB,
    packed: &[AB::Var; U32_LIMBS],
    bits: &[AB::Var; WORD_BITS],
) {
    // Re-derive the packed expression from the bits.
    let [lo, hi] = pack_word::<AB>(bits);
    // Emit one equality per limb.
    builder.assert_zeros([packed[0].into() - lo, packed[1].into() - hi]);
}

/// Wrapper around `p3_air::utils::add2` to keep this file self-contained.
///
/// See the upstream helper for the soundness argument.
#[inline]
fn add2<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::Var; U32_LIMBS],
    b: &[AB::Var; U32_LIMBS],
    c: &[AB::Expr; U32_LIMBS],
) {
    p3_air::utils::add2(builder, a, b, c);
}

/// Wrapper around `p3_air::utils::add3`.
#[inline]
fn add3<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::Var; U32_LIMBS],
    b: &[AB::Var; U32_LIMBS],
    c: &[AB::Expr; U32_LIMBS],
    d: &[AB::Expr; U32_LIMBS],
) {
    p3_air::utils::add3(builder, a, b, c, d);
}

/// Variant of `add2` where the output `a` is supplied as an expression.
///
/// # Soundness
///
/// The upstream `add2` proof needs every limb in `[0, 2^16)`.
///
/// - `b`, `c`: inherited from their callers.
/// - `a`: a sum of 16 boolean bits × `2^i`, so each limb is in `[0, 2^16)` by construction.
///
/// # Arguments
///
/// - `a`: output as a 2-limb expression.
/// - `b`: committed addend.
/// - `c`: addend expression.
///
/// # Constraint degree
///
/// Two degree-2 constraints.
#[inline]
fn add2_expr_out<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::Expr; U32_LIMBS],
    b: &[AB::Var; U32_LIMBS],
    c: &[AB::Expr; U32_LIMBS],
) {
    // Materialize 2^16 and 2^32 as field constants.
    let two_16 = <AB::Expr as PrimeCharacteristicRing>::PrimeSubfield::from_canonical_checked(
        1 << BITS_PER_LIMB,
    )
    .expect("characteristic must exceed 2^17");
    let two_32 = two_16.square();

    // 16-bit accumulator: difference of the low limbs.
    let acc_16 = a[0].dup() - b[0] - c[0].dup();
    // 32-bit accumulator: build up from the 16-bit limb plus the high limb
    // shifted by 2^16.
    let acc_32 = a[1].dup() - b[1] - c[1].dup();
    let acc = acc_16.dup() + acc_32.mul_2exp_u64(BITS_PER_LIMB as u64);

    builder.assert_zeros([
        // 32-bit overflow check: forces acc ∈ {0, -2^32} mod P.
        acc.dup() * (acc + AB::Expr::from_prime_subfield(two_32)),
        // 16-bit overflow check: forces acc_16 ∈ {0, -2^16} mod P.
        acc_16.dup() * (acc_16 + AB::Expr::from_prime_subfield(two_16)),
    ]);
}

/// Variant of `add3` where the output `a` is supplied as an expression.
///
/// # Soundness
///
/// Same argument as the two-addend variant: `a`'s limbs are in `[0, 2^16)`
/// whenever it is built from boolean-checked bits.
///
/// # Constraint degree
///
/// Two degree-3 constraints.
#[inline]
fn add3_expr_out<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::Expr; U32_LIMBS],
    b: &[AB::Var; U32_LIMBS],
    c: &[AB::Expr; U32_LIMBS],
    d: &[AB::Expr; U32_LIMBS],
) {
    // Materialize 2^16 and 2^32.
    let two_16 = <AB::Expr as PrimeCharacteristicRing>::PrimeSubfield::from_canonical_checked(
        1 << BITS_PER_LIMB,
    )
    .expect("characteristic must exceed 3 * 2^16");
    let two_32 = two_16.square();

    // 16-bit accumulator with four addends.
    let acc_16 = a[0].dup() - b[0] - c[0].dup() - d[0].dup();
    let acc_32 = a[1].dup() - b[1] - c[1].dup() - d[1].dup();
    let acc = acc_16.dup() + acc_32.mul_2exp_u64(BITS_PER_LIMB as u64);

    builder.assert_zeros([
        // Cubic check at the 32-bit level: forces acc ∈ {0, -2^32, -2*2^32}.
        acc.dup()
            * (acc.dup() + AB::Expr::from_prime_subfield(two_32))
            * (acc + AB::Expr::from_prime_subfield(two_32.double())),
        // Cubic check at the 16-bit limb level.
        acc_16.dup()
            * (acc_16.dup() + AB::Expr::from_prime_subfield(two_16))
            * (acc_16 + AB::Expr::from_prime_subfield(two_16.double())),
    ]);
}

/// Selector for the four SHA-256 "sigma" combinators.
///
/// Each variant fixes three integer amounts and whether the third operand is
/// a rotation or a logical shift.
///
/// ```text
///     BigSigma0:   ROTR_2   XOR ROTR_13  XOR ROTR_22
///     BigSigma1:   ROTR_6   XOR ROTR_11  XOR ROTR_25
///     SmallSigma0: ROTR_7   XOR ROTR_18  XOR SHR_3
///     SmallSigma1: ROTR_17  XOR ROTR_19  XOR SHR_10
/// ```
#[derive(Copy, Clone)]
enum SigmaSpec {
    BigSigma0,
    BigSigma1,
    SmallSigma0,
    SmallSigma1,
}

/// Return the rotation amounts and shift kind for a sigma variant.
///
/// # Returns
///
/// A tuple `(r1, r2, r3_or_s3, kind)`:
/// - `r1`, `r2`: rotation amounts for the first two XOR operands.
/// - `r3_or_s3`: rotation or shift amount for the third operand.
/// - `kind`: whether the third operand is a rotation or a logical shift.
#[inline]
const fn sigma_params(spec: SigmaSpec) -> (u32, u32, u32, ShiftKind) {
    match spec {
        SigmaSpec::BigSigma0 => (2, 13, 22, ShiftKind::Rotate),
        SigmaSpec::BigSigma1 => (6, 11, 25, ShiftKind::Rotate),
        SigmaSpec::SmallSigma0 => (7, 18, 3, ShiftKind::Logical),
        SigmaSpec::SmallSigma1 => (17, 19, 10, ShiftKind::Logical),
    }
}

/// Distinguishes cyclic-rotate-right from logical-shift-right.
///
/// - Rotate wraps high bits around to the low end.
/// - Logical injects zeros at the high end.
#[derive(Copy, Clone)]
enum ShiftKind {
    Rotate,
    Logical,
}

/// Assert `packed` equals `sigma_spec(bits)` in packed form.
///
/// # Algorithm
///
/// Per output bit `i` in `0..32`:
///
/// ```text
///     out_i = src_r1[i] XOR src_r2[i] XOR src_r3_or_s3[i]
/// ```
///
/// where `src_rk[i]` reads `bits[(i + rk) mod 32]` for a rotation, or
/// `bits[i + rk]` if that index is `< 32` and `0` otherwise for a logical
/// shift.
///
/// The 16 per-bit expressions in each limb are then combined via Horner into
/// a single polynomial and compared with the committed packed column.
fn assert_sigma_matches<AB: AirBuilder>(
    builder: &mut AB,
    bits: &[AB::Var; WORD_BITS],
    spec: SigmaSpec,
    packed: &[AB::Var; U32_LIMBS],
) {
    let (r1, r2, r3, kind) = sigma_params(spec);

    // Fetch the "third" operand bit with the correct shift semantics.
    let get_shifted_bit = |i: usize| -> AB::Expr {
        match kind {
            // Rotate: wrap the index around modulo 32.
            ShiftKind::Rotate => bits[(i + r3 as usize) % WORD_BITS].into(),
            // Logical shift right: inject zero once the source index runs
            // past the high end of the word.
            ShiftKind::Logical => {
                let src = i + r3 as usize;
                if src < WORD_BITS {
                    bits[src].into()
                } else {
                    AB::Expr::ZERO
                }
            }
        }
    };

    // Build one packed expression per limb via Horner from high bit to low.
    let mut built: [AB::Expr; U32_LIMBS] = [AB::Expr::ZERO, AB::Expr::ZERO];
    for (limb, slot) in built.iter_mut().enumerate() {
        // Bit range covered by this limb: [lo, hi).
        let lo = limb * BITS_PER_LIMB;
        let hi = lo + BITS_PER_LIMB;
        let mut acc = AB::Expr::ZERO;
        // Horner: fold from the high bit down so each step doubles the
        // accumulator then adds the current bit.
        for i in (lo..hi).rev() {
            // Fetch the three operand bits with their respective rotation or
            // shift amounts.
            let b1: AB::Expr = bits[(i + r1 as usize) % WORD_BITS].into();
            let b2: AB::Expr = bits[(i + r2 as usize) % WORD_BITS].into();
            let b3 = get_shifted_bit(i);
            // Arithmetic XOR3 for boolean inputs:
            //     b1 + b2 + b3 - 2*(b1*b2 + b1*b3 + b2*b3) + 4*b1*b2*b3
            let bit_value = b1.xor3(&b2, &b3);
            // Horner step: shift the accumulator left by 1 then add the bit.
            acc = acc.double() + bit_value;
        }
        *slot = acc;
    }

    // Destructure the built expressions and emit one equality per limb.
    let [built_lo, built_hi] = built;
    builder.assert_zeros([packed[0].into() - built_lo, packed[1].into() - built_hi]);
}

/// Assert `packed` equals `Ch(e, f, g)` in packed form.
///
/// # Algorithm
///
/// The two AND-terms are disjoint on boolean inputs, so the XOR collapses to
/// an addition:
///
/// ```text
///     Ch_i = e_i * f_i + (1 - e_i) * g_i
/// ```
///
/// That bit expression has degree 2, so the packed constraint has degree 2.
fn assert_ch_matches<AB: AirBuilder>(
    builder: &mut AB,
    e: &[AB::Var; WORD_BITS],
    f: &[AB::Var; WORD_BITS],
    g: &[AB::Var; WORD_BITS],
    packed: &[AB::Var; U32_LIMBS],
) {
    let mut built: [AB::Expr; U32_LIMBS] = [AB::Expr::ZERO, AB::Expr::ZERO];
    for (limb, slot) in built.iter_mut().enumerate() {
        let lo = limb * BITS_PER_LIMB;
        let hi = lo + BITS_PER_LIMB;
        let mut acc = AB::Expr::ZERO;
        // Horner, high to low bit.
        for i in (lo..hi).rev() {
            // Pull the three operand bits into expressions.
            let ei: AB::Expr = e[i].into();
            let fi: AB::Expr = f[i].into();
            let gi: AB::Expr = g[i].into();
            // Degree-2 bit identity equivalent to (e AND f) XOR (NOT e AND g).
            let ch_i = ei.dup() * fi + (AB::Expr::ONE - ei) * gi;
            // Horner step.
            acc = acc.double() + ch_i;
        }
        *slot = acc;
    }

    let [built_lo, built_hi] = built;
    builder.assert_zeros([packed[0].into() - built_lo, packed[1].into() - built_hi]);
}

/// Assert `packed` equals `Maj(a, b, c)` in packed form.
///
/// # Algorithm
///
/// The boolean majority of three inputs satisfies:
///
/// ```text
///     Maj_i = a_i * b_i + c_i * (a_i XOR b_i)
///           = a_i * b_i + c_i * (a_i + b_i - 2 * a_i * b_i)
/// ```
///
/// That expression has degree 3 per bit.
fn assert_maj_matches<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::Var; WORD_BITS],
    b: &[AB::Var; WORD_BITS],
    c: &[AB::Var; WORD_BITS],
    packed: &[AB::Var; U32_LIMBS],
) {
    let mut built: [AB::Expr; U32_LIMBS] = [AB::Expr::ZERO, AB::Expr::ZERO];
    for (limb, slot) in built.iter_mut().enumerate() {
        let lo = limb * BITS_PER_LIMB;
        let hi = lo + BITS_PER_LIMB;
        let mut acc = AB::Expr::ZERO;
        // Horner, high to low bit.
        for i in (lo..hi).rev() {
            // Pull the three operand bits into expressions.
            let ai: AB::Expr = a[i].into();
            let bi: AB::Expr = b[i].into();
            let ci: AB::Expr = c[i].into();
            // Degree-3 identity: `a*b + c * xor(a, b)` matches the bitwise
            // majority on boolean inputs.
            let maj_i = ai.dup() * bi.dup() + ci * ai.xor(&bi);
            // Horner step.
            acc = acc.double() + maj_i;
        }
        *slot = acc;
    }

    let [built_lo, built_hi] = built;
    builder.assert_zeros([packed[0].into() - built_lo, packed[1].into() - built_hi]);
}
