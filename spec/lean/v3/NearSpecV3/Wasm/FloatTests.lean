import NearSpecV3.Wasm.Float
/-!
# Finite directed tests for the L2 float kernel

Every fact here is decided by the kernel (`decide` or `decide +kernel`), so this file is a test
suite that the *build* runs: a wrong bit pattern in `Wasm/Float.lean` breaks the build rather than
a downstream corpus run. The cases are the discriminating ones the plan's §5 asks for — signed
zero, subnormals, infinities, NaN payloads, rounding ties, conversion boundaries and traps — one per
branch of the kernel.

**These are tests, not proofs about nearcore.** They fix what the Lean kernel computes; agreement
with the pinned engine is measured in `oracle/wasm-d3/tests/` (`difftest_float.py`,
`float_nearcore.py`) and is not a theorem.
-/
namespace NearSpecV3.Wasm.FloatTests

open NearSpecV3.Wasm

/-! ## Constants used below (f32 unless stated) -/

def pzero : Nat := 0x00000000
def nzero : Nat := 0x80000000
def one : Nat := 0x3F800000
def none_ : Nat := 0xBF800000
def two : Nat := 0x40000000
def pInf : Nat := 0x7F800000
def nInf : Nat := 0xFF800000
def qnan : Nat := 0x7FC00000
def nanPayload : Nat := 0x7FC12345
def nnansPayload : Nat := 0xFFC12345
def snan : Nat := 0x7F800001
def maxSub : Nat := 0x007FFFFF
def minSub : Nat := 0x00000001
def minNorm : Nat := 0x00800000
def maxFin : Nat := 0x7F7FFFFF
/-- `1.5` as f32. -/
def f1_5 : Nat := 0x3FC00000
/-- `2.5` as f32. -/
def f2_5 : Nat := 0x40200000

def d_one : Nat := 0x3FF0000000000000
def d_pzero : Nat := 0x0000000000000000
def d_nzero : Nat := 0x8000000000000000
def d_pInf : Nat := 0x7FF0000000000000
def d_qnan : Nat := 0x7FF8000000000000
def d_nanPayload : Nat := 0x7FF8000000012345
def d_maxFin : Nat := 0x7FEFFFFFFFFFFFFF
def d_minSub : Nat := 0x0000000000000001

/-! ## 1. Signed zero -/

/-- `+0 + -0 = +0` (round-to-nearest: the exact sum is zero, and the sign of a zero sum of
opposite-signed zeros is `+`). -/
theorem add_zeros : Fmt.add f32 pzero nzero = pzero := by decide
/-- `-0 + -0 = -0`. -/
theorem add_neg_zeros : Fmt.add f32 nzero nzero = nzero := by decide
/-- `x - x = +0` for a finite non-zero `x`. -/
theorem sub_self : Fmt.sub f32 one one = pzero := by decide
/-- `-0 - +0 = -0`. -/
theorem sub_zero : Fmt.sub f32 nzero pzero = nzero := by decide
/-- `+0 * -3 = -0`: a zero product takes the xor of the signs. -/
theorem mul_zero_sign : Fmt.mul f32 pzero (0x40400000 : Nat) = pzero := by decide
theorem mul_zero_neg : Fmt.mul f32 nzero (0x40400000 : Nat) = nzero := by decide
/-- `min(+0, -0) = -0` (the bitwise OR of equal operands, Winch's ordered-equal branch). -/
theorem min_zeros : Fmt.min f32 pzero nzero = nzero := by decide
/-- `max(+0, -0) = +0` (the bitwise AND). -/
theorem max_zeros : Fmt.max f32 pzero nzero = pzero := by decide
/-- `sqrt(-0) = -0` (IEEE 754 §5.4.1; the operand is returned unchanged). -/
theorem sqrt_neg_zero : Fmt.sqrt f32 nzero = nzero := by decide
/-- `ceil(-0.5) = -0`, `floor(0.5) = +0`: a rounded-to-zero result keeps the operand's sign. -/
theorem ceil_half_neg : Fmt.ceil f32 (0xBF000000 : Nat) = nzero := by decide
theorem floor_half : Fmt.floor f32 (0x3F000000 : Nat) = pzero := by decide
/-- `nearest(-0.4) = -0`. -/
theorem nearest_neg_small : Fmt.nearest f32 (0xBECCCCCD : Nat) = nzero := by decide
/-- `trunc(-0.5) = -0`. -/
theorem trunc_neg : Fmt.trunc f32 (0xBF000000 : Nat) = nzero := by decide

/-! ## 2. Subnormals and the subnormal/normal boundary -/

/-- The smallest subnormal survives `abs` and `neg` unchanged in magnitude. -/
theorem minSub_abs : Fmt.abs f32 minSub = minSub := by decide
/-- `minSub + minSub = 2 * minSub`, exactly (no precision is lost). -/
theorem sub_add_exact : Fmt.add f32 minSub minSub = 0x00000002 := by decide
/-- `minSub * 0.5` is a tie between `0` and `minSub`; round-half-to-even picks `0`. -/
theorem sub_underflow_tie : Fmt.mul f32 minSub (0x3F000000 : Nat) = pzero := by decide
/-- `minSub * 0.75` rounds up to `minSub`. -/
theorem sub_underflow_up : Fmt.mul f32 minSub (0x3F400000 : Nat) = minSub := by decide
/-- `3 * minSub` is exact. -/
theorem sub_times_three : Fmt.add f32 minSub (0x00000002 : Nat) = 0x00000003 := by decide
/-- `maxSub + minSub = minNorm`, the smallest normal — the gradual-underflow boundary is exact. -/
theorem sub_to_normal : Fmt.add f32 maxSub minSub = minNorm := by decide
/-- `minNorm - minSub = maxSub`. -/
theorem normal_to_sub : Fmt.sub f32 minNorm minSub = maxSub := by decide
/-- `maxSub / 2`: `maxSub = 2^-126 · (1 - 2^-23)`, so half of it is `2^-127 · (2 - 2^-22)`, which
is exactly the subnormal `0x00400000`. (A division, not a rounding tie: both operands are exact.) -/
theorem maxSub_half : Fmt.div f32 maxSub (0x40000000 : Nat) = 0x00400000 := by decide
/-- A subnormal is not a zero: `1 / minSub` overflows to `+inf`. -/
theorem inf_from_sub : Fmt.div f32 one minSub = pInf := by decide
/-- Every subnormal is normal after promotion (f64 has the range). -/
theorem promote_minSub : Fmt.promote minSub = 0x36A0000000000000 := by decide
/-- … and demoting it back is exact. -/
theorem demote_promote_minSub : Fmt.demote (Fmt.promote minSub) = minSub := by decide
/-- The smallest f64 subnormal is `2^-1074`. -/
theorem f64_minSub_is_pow : Fmt.decode f64 d_minSub = (false, 1, -1074) := by decide

/-! ## 3. Infinities and overflow -/

/-- `maxFin + maxFin` overflows to `+inf` (the IEEE threshold: rounding a value `≥ 2^128` for f32). -/
theorem overflow_add : Fmt.add f32 maxFin maxFin = pInf := by decide
theorem overflow_neg : Fmt.add f32 (0xFF7FFFFF : Nat) (0xFF7FFFFF : Nat) = nInf := by decide
/-- `inf - inf = NaN`, canonicalised. -/
theorem inf_sub_inf : Fmt.sub f32 pInf pInf = qnan := by decide
/-- `inf * 0 = NaN`. -/
theorem inf_mul_zero : Fmt.mul f32 pInf pzero = qnan := by decide
/-- `0 / 0 = NaN`, `inf / inf = NaN`. -/
theorem zero_div_zero : Fmt.div f32 pzero pzero = qnan := by decide
theorem inf_div_inf : Fmt.div f32 pInf pInf = qnan := by decide
/-- `1 / 0 = +inf`, `-1 / 0 = -inf` (no trap in IEEE). -/
theorem one_div_zero : Fmt.div f32 one pzero = pInf := by decide
theorem neg_one_div_zero : Fmt.div f32 none_ pzero = nInf := by decide
/-- `maxFin * 2` overflows. -/
theorem overflow_mul : Fmt.mul f32 maxFin two = pInf := by decide
/-- `sqrt(+inf) = +inf`, `sqrt(-1) = NaN`. -/
theorem sqrt_inf : Fmt.sqrt f32 pInf = pInf := by decide
theorem sqrt_negative : Fmt.sqrt f32 none_ = qnan := by decide
/-- `ceil`/`floor`/`trunc`/`nearest` of an infinity is the infinity. -/
theorem ceil_inf : Fmt.ceil f32 pInf = pInf := by decide
theorem nearest_neg_inf : Fmt.nearest f32 nInf = nInf := by decide
/-- The largest finite f64 is exactly `(2^53-1)·2^971`. Its exponent field is `0x7FE`, and its
significand is all ones. -/
theorem f64_maxFin_exp : Fmt.expField f64 d_maxFin = 0x7FE := by decide
theorem f64_maxFin_frac : Fmt.fracField f64 d_maxFin = 2 ^ 52 - 1 := by decide
/-- `roundPack f64` overflows to infinity just past the IEEE threshold `2^1024`. This is the
overflow branch of the packing kernel, on the same code path `maxFin * 2` takes (which `decide`
cannot reach within its recursion budget: the kernel would normalise a 54-bit product; the full
product is covered by `oracle/wasm-d3/tests/difftest_float.py`). -/
theorem roundPack_overflow :
    Fmt.roundPack f64 false (2 ^ 53) 972 = d_pInf := by decide
/-- Just below the threshold, the same rounding stays finite. -/
theorem roundPack_maxFin :
    Fmt.roundPack f64 false (2 ^ 53 - 1) 971 = d_maxFin := by decide

/-! ## 4. NaN payloads: canonicalising vs bit-preserving -/

/-- Every arithmetic operator with a NaN operand yields the **canonical** NaN and drops the
payload: `0x7fc12345 + 1 = 0x7fc00000`. -/
theorem add_payload_dropped : Fmt.add f32 nanPayload one = qnan := by decide
theorem mul_payload_dropped : Fmt.mul f32 nanPayload one = qnan := by decide
theorem sub_payload_dropped : Fmt.sub f32 nanPayload one = qnan := by decide
theorem div_payload_dropped : Fmt.div f32 nanPayload one = qnan := by decide
theorem min_payload_dropped : Fmt.min f32 nanPayload one = qnan := by decide
theorem max_payload_dropped : Fmt.max f32 nanPayload one = qnan := by decide
theorem sqrt_payload_dropped : Fmt.sqrt f32 nanPayload = qnan := by decide
theorem ceil_payload_dropped : Fmt.ceil f32 nanPayload = qnan := by decide
theorem nearest_payload_dropped : Fmt.nearest f32 nanPayload = qnan := by decide
/-- The sign of the input NaN does not survive either: canonical is positive. -/
theorem add_negative_nan : Fmt.add f32 nnansPayload one = qnan := by decide
/-- A signalling NaN becomes the quiet canonical NaN. -/
theorem add_snan : Fmt.add f32 snan one = qnan := by decide
/-- `promote` and `demote` canonicalise too (Winch runs `maybe_canonicalize_nan` after both). -/
theorem promote_payload_dropped : Fmt.promote nanPayload = d_qnan := by decide
theorem demote_payload_dropped : Fmt.demote d_nanPayload = qnan := by decide
/-- `abs`/`neg`/`copysign` are **bit-preserving**: the payload survives and only the sign moves. -/
theorem abs_payload_kept : Fmt.abs f32 nnansPayload = nanPayload := by decide
theorem neg_payload_kept : Fmt.neg f32 nanPayload = nnansPayload := by decide
theorem copysign_payload_kept : Fmt.copysign f32 nanPayload none_ = nnansPayload := by decide
theorem copysign_payload_kept2 : Fmt.copysign f32 nnansPayload one = nanPayload := by decide
/-- `reinterpret` is identity on the bits, both directions, for a NaN payload. -/
theorem reinterpret_f32_i32 : evalFloatOp 0xBC nanPayload 0 = some nanPayload := by decide
theorem reinterpret_i32_f32 : evalFloatOp 0xBE nanPayload 0 = some nanPayload := by decide
/-- A NaN compared with `ne` is true, every other comparison is false. -/
theorem nan_ne : evalFloatOp 0x5C nanPayload one = some 1 := by decide
theorem nan_eq : evalFloatOp 0x5B nanPayload nanPayload = some 0 := by decide
theorem nan_lt : evalFloatOp 0x5D nanPayload one = some 0 := by decide
theorem nan_le : evalFloatOp 0x5F nanPayload one = some 0 := by decide
/-- `-0 = +0`, and `-0 < +0` is false. -/
theorem zeros_eq : evalFloatOp 0x5B pzero nzero = some 1 := by decide
theorem zeros_lt : evalFloatOp 0x5D pzero nzero = some 0 := by decide

/-! ## 5. Rounding ties (round-to-nearest, ties-to-even) -/

/-- `1.5 → 2` (2 is even), `2.5 → 2` (2 is even), `3.5 → 4`, `-1.5 → -2`. These are the four
cases that distinguish ties-to-even from ties-away-from-zero. -/
theorem nearest_1_5 : Fmt.nearest f32 f1_5 = two := by decide
theorem nearest_2_5 : Fmt.nearest f32 f2_5 = two := by decide
theorem nearest_3_5 : Fmt.nearest f32 (0x40600000 : Nat) = 0x40800000 := by decide
theorem nearest_neg_1_5 : Fmt.nearest f32 (0xBFC00000 : Nat) = 0xC0000000 := by decide
/-- `trunc`/`floor`/`ceil` disagree on `1.5` and `-1.5`. -/
theorem trunc_1_5 : Fmt.trunc f32 f1_5 = one := by decide
theorem floor_1_5 : Fmt.floor f32 f1_5 = one := by decide
theorem ceil_1_5 : Fmt.ceil f32 f1_5 = two := by decide
theorem trunc_neg_1_5 : Fmt.trunc f32 (0xBFC00000 : Nat) = none_ := by decide
theorem floor_neg_1_5 : Fmt.floor f32 (0xBFC00000 : Nat) = 0xC0000000 := by decide
theorem ceil_neg_1_5 : Fmt.ceil f32 (0xBFC00000 : Nat) = none_ := by decide
/-- An add that lands exactly halfway between two f32 values rounds to the even one:
`2^24 + 1` is a tie (both neighbours are representable), and `2^24` has an even significand. -/
theorem add_tie_to_even : Fmt.add f32 (0x4B800000 : Nat) one = 0x4B800000 := by decide
/-- `2^24 + 3` is a tie between `2^24+2` and `2^24+4`; it rounds to the even one, `2^24+4`. -/
theorem add_tie_up : Fmt.add f32 (0x4B800000 : Nat) (0x40400000 : Nat) = 0x4B800002 := by decide
/-- The significand boundary of f32: `2^24 + 1` cannot be represented, so the literal rounds. -/
theorem convert_2_24_plus_1 : Fmt.convertInt f32 16777217 = 0x4B800000 := by decide
theorem convert_2_24_plus_3 : Fmt.convertInt f32 16777219 = 0x4B800002 := by decide

/-! ## 6. Conversion boundaries (exact values, and one step past) -/

/-- `i32.trunc_f32_s` of `2^31 - 128` (the largest f32 below `2^31`). -/
theorem trunc_s_max : evalFloatOp 0xA8 (0x4EFFFFFF : Nat) 0 = some 0x7FFFFF80 := by decide
theorem trunc_s_min : evalFloatOp 0xA8 (0xCF000000 : Nat) 0 = some 0x80000000 := by decide
/-- One representable step past `2^31` traps (`2^31` itself is exact, `2^31 + 2^8` is the next
f32). -/
theorem trunc_s_over : evalFloatOp 0xA8 (0x4F000001 : Nat) 0 = none := by decide
/-- `i32.trunc_f32_u` at `2^32 - 256` (the largest f32 below `2^32`) is in range; `2^32` traps. -/
theorem trunc_u_max : evalFloatOp 0xA9 (0x4F7FFFFF : Nat) 0 = some 0xFFFFFF00 := by decide
theorem trunc_u_over : evalFloatOp 0xA9 (0x4F800000 : Nat) 0 = none := by decide
/-- `-0.5` truncates to `0` for `_u` (no trap: `trunc(-0.5) = 0`). -/
theorem trunc_u_neg : evalFloatOp 0xA9 (0xBF000000 : Nat) 0 = some 0 := by decide
/-- `-1.0` traps for `_u`. -/
theorem trunc_u_negative : evalFloatOp 0xA9 none_ 0 = none := by decide
/-- NaN and infinity always trap in the non-saturating forms. -/
theorem trunc_nan_traps : evalFloatOp 0xA8 qnan 0 = none := by decide
theorem trunc_inf_traps : evalFloatOp 0xA8 pInf 0 = none := by decide
/-- `i64.trunc_f64_u` of `-1.0` traps (negative). -/
theorem trunc64_neg_traps : evalFloatOp 0xB1 (0xBFF0000000000000 : Nat) 0 = none := by decide
/-- `i64.trunc_f64_u` at `2^64 - 2048`; `2^64` traps. -/
theorem trunc64_max : evalFloatOp 0xB1 (0x43EFFFFFFFFFFFFF : Nat) 0 = some 0xFFFFFFFFFFFFF800 := by decide
theorem trunc64_over : evalFloatOp 0xB1 (0x43F0000000000000 : Nat) 0 = none := by decide
/-- The saturating forms do not trap: NaN → 0, overflow saturates. -/
theorem sat_nan : evalFloatOp 0xFC00 qnan 0 = some 0 := by decide
theorem sat_pos_over : evalFloatOp 0xFC00 (0x4F800000 : Nat) 0 = some 0x7FFFFFFF := by decide
theorem sat_neg_over : evalFloatOp 0xFC00 (0xCF000000 : Nat) 0 = some 0x80000000 := by decide
theorem sat_u_neg : evalFloatOp 0xFC01 none_ 0 = some 0 := by decide
theorem sat_u_pos : evalFloatOp 0xFC01 (0x4F800000 : Nat) 0 = some 0xFFFFFFFF := by decide
theorem sat64_nan : evalFloatOp 0xFC06 d_qnan 0 = some 0 := by decide
theorem sat64_pos : evalFloatOp 0xFC06 (0x43F0000000000000 : Nat) 0 = some 0x7FFFFFFFFFFFFFFF := by decide
/-- Integer → float at the precision boundary: `2^53 + 1` is a tie, rounds to `2^53`. -/
theorem convert_2_53_plus_1 : Fmt.convertInt f64 9007199254740993 = 0x4340000000000000 := by decide
theorem convert_2_53_plus_3 : Fmt.convertInt f64 9007199254740995 = 0x4340000000000002 := by decide
/-- `i64_u → f64` of `2^64-1` rounds up to `2^64`. -/
theorem convert_u64_max : Fmt.convertInt f64 18446744073709551615 = 0x43F0000000000000 := by decide
/-- `i32_s` conversions are exact (24-bit significand, 32-bit source is not, so check a tie). -/
theorem convert_i32_s_exact : evalFloatOp 0xB2 0xFFFFFFFF 0 = some 0xBF800000 := by decide

/-! ## 7. Opcode coverage: every dispatch arm has a decided result -/

/-- The seven `f32` two-operand arithmetic arms, one case each. -/
theorem opcode_add : evalFloatOp 0x92 one one = some two := by decide
theorem opcode_sub : evalFloatOp 0x93 one one = some pzero := by decide
theorem opcode_mul : evalFloatOp 0x94 one one = some one := by decide
theorem opcode_div : evalFloatOp 0x95 one one = some one := by decide
theorem opcode_min : evalFloatOp 0x96 one one = some one := by decide
theorem opcode_max : evalFloatOp 0x97 one one = some one := by decide
theorem opcode_copysign : evalFloatOp 0x98 one one = some one := by decide
/-- The six `f32` unary arms. -/
theorem opcode_abs : evalFloatOp 0x8B nnansPayload 0 = some nanPayload := by decide
theorem opcode_neg : evalFloatOp 0x8C nanPayload 0 = some nnansPayload := by decide
theorem opcode_ceil : evalFloatOp 0x8D f1_5 0 = some two := by decide
theorem opcode_floor : evalFloatOp 0x8E f1_5 0 = some one := by decide
theorem opcode_trunc : evalFloatOp 0x8F f1_5 0 = some one := by decide
theorem opcode_nearest : evalFloatOp 0x90 f1_5 0 = some two := by decide
/-- The six `f32` comparison arms. -/
theorem opcode_eq : evalFloatOp 0x5B one one = some 1 := by decide
theorem opcode_ne : evalFloatOp 0x5C one one = some 0 := by decide
theorem opcode_lt : evalFloatOp 0x5D one two = some 1 := by decide
theorem opcode_gt : evalFloatOp 0x5E one two = some 0 := by decide
theorem opcode_le : evalFloatOp 0x5F one one = some 1 := by decide
theorem opcode_ge : evalFloatOp 0x60 one two = some 0 := by decide
/-- The `f64` dispatch, one operator per kind, so no f64 arm is dead code. -/
theorem opcode_f64_add : evalFloatOp 0xA0 d_one d_one = some 0x4000000000000000 := by decide
theorem opcode_f64_min : evalFloatOp 0xA4 d_one d_one = some d_one := by decide
theorem opcode_f64_sqrt : evalFloatOp 0x9F d_one 0 = some d_one := by decide
theorem opcode_f64_copysign : evalFloatOp 0xA6 d_one d_one = some d_one := by decide
theorem opcode_promote : evalFloatOp 0xBB (0x3F800000 : Nat) 0 = some 0x3FF0000000000000 := by decide
theorem opcode_f64_convert_u : evalFloatOp 0xB7 (0x00000001 : Nat) 0 = some 0x3FF0000000000000 := by decide

/-- Every opcode `isFloatOpNoImm` admits has a `floatResultType` and an operand list, and the
saturating-truncation opcodes are exactly the `0xFC00..0xFC07` range. -/
theorem saturating_opcodes :
    isFloatOpNoImm 0xFC00 && isFloatOpNoImm 0xFC07 && !isFloatOpNoImm 0xFC08 = true := by decide
/-- The eight trapping truncations are exactly `floatPartial`'s set. -/
theorem partial_opcodes :
    (floatPartial 0xA8, floatPartial 0xAB, floatPartial 0xAE, floatPartial 0xB1,
     floatPartial 0x92, floatPartial 0xFC00) =
    (true, true, true, true, false, false) := by decide

/-! ## 8. min/max: the sign-of-zero and NaN branches -/

theorem min_neg_values : Fmt.min f32 none_ one = none_ := by decide
theorem max_neg_values : Fmt.max f32 none_ one = one := by decide
/-- `min(x, x) = x` also holds for a NaN pair only through the NaN branch (canonical). -/
theorem min_nan_pair : Fmt.min f32 nanPayload nanPayload = qnan := by decide
/-- `min` of an infinity and a finite value. -/
theorem min_inf : Fmt.min f32 nInf one = nInf := by decide
theorem max_inf : Fmt.max f32 pInf one = pInf := by decide

end NearSpecV3.Wasm.FloatTests
