/-!
# Exact IEEE 754 binary64 for the non-negative values of congestion control

Leaf module of `near/pv86/chunk-validation/v0`. The only consensus-relevant
floating point in chunk application is in `core/primitives/src/congestion_info.rs`
(inventory: docs/research/chunk-validation-boundary.md §9.3):

* `clamped_f64_fraction` :474-477 — `if max as u128 ≤ v {1.0} else {(v as f64) / (max as f64)}`;
* `congestion_level` :44-54 — `f64::max` of four such fractions;
* `is_fully_congested` :95-100 — `level == 1.0`;
* `mix` :484-502 — `(left as f64 * (1.0 − r) + right as f64 * r).round() as u64`.

So only `u128 as f64`, `u64 as f64`, `/`, `*`, `−`, `+`, `max`, `==`, `round`
(half away from zero) and `f64 as u64` (saturating, truncating) occur, all on
non-negative finite values: no NaN (`max > 0` is asserted), no infinities, no
FMA contraction in Rust. IEEE 754 §4.3/§5 define every one of these operations
as "the exact real result, rounded to nearest-even onto the binary64 grid"
(`as` casts from integers are round-to-nearest-even as well; `round` and the
float-to-int cast are exact integer functions of a double). This module is a
transcription of that definition.

**Representation.** `⟨m, e⟩` denotes `m · 2^e`; canonical forms are `⟨0, 0⟩`
(+0.0) and normal numbers `2^52 ≤ m < 2^53`. Every operation forms the exact
rational result `p / q` (`p q : Nat`) and rounds it with `ofRat`.

**Value ranges (why no subnormals / overflow).** Binary64 normals cover
`2^-1022 … (2 − 2^-52)·2^1023`; with this representation that is
`−1074 ≤ e ≤ 971`. Reachable values: integers `< 2^128` (`e ≤ 76`); fractions
`v / max` with `1 ≤ v < max < 2^64`, hence `≥ 2^-64`; `1 − r` with `r` a double
in `[0, 1]`, which is `0` or `≥ 2^-53`; products of a `u64` and such a value
(`≥ 2^-117` or 0, `< 2^64`); sums of two such products. All non-zero results
lie in `[2^-117, 2^129)`, far inside the normal range, so `ofRat` never needs
the subnormal or overflow branches of IEEE rounding and does not implement them.
(`toBits` is only meaningful on that range.)

**Kernel reducibility.** Only `Nat`/`Int` arithmetic; `bitLen` is structurally
recursive on an explicit fuel of 4096 (every numerator/denominator formed here
is `< 2^400`: exponents are bounded as above and operands have ≤ 53-bit
mantissas, so the cross products of `add`/`div` stay far below `2^4096`).
-/

namespace NearSpecV3

/-- A non-negative finite binary64 value `m · 2^e` (canonical: `m = 0, e = 0`
or `2^52 ≤ m < 2^53`). -/
structure F64 where
  m : Nat
  e : Int
  deriving DecidableEq, Repr

namespace F64

/-- Number of binary digits of `n` (`bitLen 0 = 0`), fuel-bounded (see module doc). -/
def bitLenF : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n = 0 then 0 else 1 + bitLenF f (n / 2)

def bitLen (n : Nat) : Nat := bitLenF 4096 n

def two52 : Nat := 4503599627370496
def two53 : Nat := 9007199254740992
def u64Max : Nat := 18446744073709551615

def zero : F64 := ⟨0, 0⟩
def one : F64 := ⟨two52, -52⟩

/-- Round `num / den · 2^e` to nearest, ties to even, assuming
`2^52 ≤ num / den < 2^53`. A carry to `2^53` renormalizes. -/
def roundStep (num den : Nat) (e : Int) : F64 :=
  let q := num / den
  let r := num % den
  let up := decide (den < 2 * r) || (decide (2 * r = den) && q % 2 == 1)
  let m := if up then q + 1 else q
  if m = two53 then ⟨two52, e + 1⟩ else ⟨m, e⟩

/-- IEEE 754 round-to-nearest-even of the non-negative rational `p / q`
(normal range; `q = 0` is unreachable and yields `zero`). -/
def ofRat (p q : Nat) : F64 :=
  if p = 0 ∨ q = 0 then zero else
  -- p ∈ [2^(a-1), 2^a), q ∈ [2^(b-1), 2^b) with a = bitLen p, b = bitLen q,
  -- so p / q ∈ (2^(a-b-1), 2^(a-b+1)) and p / (q·2^e0) ∈ (2^52, 2^54).
  let e0 : Int := (bitLen p : Int) - (bitLen q : Int) - 53
  let num := if e0 < 0 then p * 2 ^ (-e0).toNat else p
  let den := if e0 < 0 then q else q * 2 ^ e0.toNat
  if two53 ≤ num / den then roundStep num (2 * den) (e0 + 1) else roundStep num den e0

/-- The exact value as a fraction `(num, den)`. -/
def toRat (x : F64) : Nat × Nat :=
  if x.e < 0 then (x.m, 2 ^ (-x.e).toNat) else (x.m * 2 ^ x.e.toNat, 1)

/-- `n as f64` for `n : u64 / u128` (round to nearest, ties to even). -/
def ofNat (n : Nat) : F64 := ofRat n 1

def mul (a b : F64) : F64 :=
  let (na, da) := a.toRat
  let (nb, db) := b.toRat
  ofRat (na * nb) (da * db)

/-- `a / b` (`b ≠ 0`). -/
def div (a b : F64) : F64 :=
  let (na, da) := a.toRat
  let (nb, db) := b.toRat
  ofRat (na * db) (da * nb)

def add (a b : F64) : F64 :=
  let (na, da) := a.toRat
  let (nb, db) := b.toRat
  ofRat (na * db + nb * da) (da * db)

/-- `a − b` for `a ≥ b` (the only use is `1.0 − r` with `r ≤ 1`; truncates at 0 otherwise). -/
def sub (a b : F64) : F64 :=
  let (na, da) := a.toRat
  let (nb, db) := b.toRat
  ofRat (na * db - nb * da) (da * db)

/-- `a ≤ b` on values. -/
def le (a b : F64) : Bool :=
  let (na, da) := a.toRat
  let (nb, db) := b.toRat
  decide (na * db ≤ nb * da)

/-- `f64::max` (no NaN): the larger value. -/
def max (a b : F64) : F64 := if le a b then b else a

/-- `==` on doubles: canonical forms are unique, so structural equality. -/
def beq (a b : F64) : Bool := decide (a = b)

/-- The exact integer `f64::round(x)` (half away from zero; `x ≥ 0`). -/
def roundNat (x : F64) : Nat :=
  let (n, d) := x.toRat
  if d ≤ 2 * (n % d) then n / d + 1 else n / d

/-- `f64::round` as a double (the rounded integer is representable). -/
def round (x : F64) : F64 := ofNat (roundNat x)

/-- `x as u64`: truncation toward zero, saturating at `u64::MAX` (`x ≥ 0`). -/
def asU64 (x : F64) : Nat :=
  let (n, d) := x.toRat
  min (n / d) u64Max

/-- IEEE 754 bit pattern (`f64::to_bits`) of a canonical value in the normal range. -/
def toBits (x : F64) : Nat :=
  if x.m = 0 then 0 else (x.e + 1075).toNat * two52 + (x.m - two52)

/-! ## Sanity facts (kernel-checked) -/

theorem one_bits : toBits one = 0x3ff0000000000000 := by decide
theorem ofNat_one : ofNat 1 = one := by decide
theorem ofNat_two53_succ : ofNat (two53 + 1) = ofNat two53 := by decide
theorem ofNat_two53_add3 : ofNat (two53 + 3) = ofNat (two53 + 4) := by decide

end F64
end NearSpecV3
