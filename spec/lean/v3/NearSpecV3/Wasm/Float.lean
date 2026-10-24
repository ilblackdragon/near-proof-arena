import NearSpecV3.Wasm.Numerics
import NearSpecV3.Wasm.Syntax
/-!
# NEAR WASM (L2): exact IEEE 754 binary32 / binary64 over bit patterns

This module is the **additive** float domain of the chunk-transition specification. It is written
from the bit pattern up (no `Float`, no `Float32`, no `native_decide`), so every operation is a
kernel-computable `Nat` function and every claim below is checked by `decide` or proved.

## What the pinned target does

nearcore 2.13.4 (`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86) executes Wasm through
wasmtime 45.0.0 with `Strategy::Winch` on x86_64 and `cranelift_nan_canonicalization(true)`
(`runtime/near-vm-runner/src/wasmtime_runner/mod.rs:512-536`). Consequences, each cited to the
pinned source:

* **NaNs are canonicalised, not propagated.** Winch emits `maybe_canonicalize_nan` after every
  operation that can produce a NaN (`winch-codegen-45.0.0/src/visitor.rs:602-960,1159`, and
  `isa/x64/masm.rs:716-738`): if the result is unordered, the register is overwritten with
  `CANONICAL_NAN_F32 = 0x7fc00000` / `CANONICAL_NAN_F64 = 0x7ff8000000000000`
  (`winch-codegen-45.0.0/src/masm.rs:16-17`). nearcore tests exactly this bit pattern
  (`wasmtime_runner/mod.rs:1243-1290`). Therefore `add/sub/mul/div/min/max/sqrt/ceil/floor/
  trunc/nearest`, `demote`, `promote` and the truncating conversions produce `+qNaN`
  (sign 0, zero payload) whenever the mathematical result is NaN — payloads are **not**
  propagated.
* **Bit-preserving operations do not canonicalise.** `abs`, `neg`, `copysign` are sign/magnitude
  bit operations in Winch (`winch-codegen-45.0.0/src/isa/x64/masm.rs:607-690`) with no
  canonicalisation pass, and `reinterpret` is a register reinterpretation (`masm.rs:1310-1328`).
  These preserve NaN payloads and signs.
* **Rounding is round-to-nearest, ties-to-even.** Wasm `f*.nearest` uses `RoundingMode::Nearest`
  → x86 `roundss/roundsd` imm 0 (`winch-codegen-45.0.0/src/isa/x64/asm.rs:1565-1588`); add/sub/
  mul/div are the SSE operations, which are RN-even on x86.
* **Traps.** Non-saturating float→int conversions trap on NaN or out-of-range values; wasmtime's
  `BadConversionToInteger` maps to `WasmTrap::IllegalArithmetic`
  (`wasmtime_runner/mod.rs:393`, `wasmtime_runner/trap_classification.rs:18`). `trunc_sat` never
  traps: NaN→0, ±∞ and out-of-range saturate.
* **Gas.** finite-wasm 0.6.1 classifies every float operator as *pure* except the eight trapping
  truncations, which are `cvtop_partial` (`finite-wasm-0.6.1/src/instruction_categories.rs:168-178`
  and `src/gas/mod.rs:419-420`). Each operator costs one `regular_op_cost`, whichever class it is
  in; at PV86 that is 822,756
  (`core/parameters/res/runtime_configs/parameters.snap:110`, `wasm_regular_op_cost 822_756`, last
  changed by `49.yaml:1`). Note the class is not what sets the price: `pure` means the operator
  merges into the surrounding instrumentation point, `cvtop_partial` that it opens its own.

## Representation

A float is its bit pattern as a `Nat` (`0 ≤ b < 2^w`). `Fmt` names a binary interchange format.
Values decode to `(sign, m, e)` meaning `(-1)^sign · m · 2^e`, with `m = 0` for a zero and `m` the
exact significand otherwise (`2^(p-1) ≤ m < 2^p` for normals, `m < 2^(p-1)` for subnormals).

`roundPackS` is the single rounding kernel: it rounds `(-1)^s · (m · 2^e + ε)`,
`0 ≤ ε < 2^e`, to `f` with round-to-nearest-ties-to-even, a sticky bit for division/square root,
gradual underflow, and overflow to infinity at the IEEE threshold.
-/

namespace NearSpecV3.Wasm

/-! ## Formats -/

/-- A binary interchange format: total width `w`, precision `p` (significand bits including the
hidden bit), exponent-field width `eb`. -/
structure Fmt where
  w : Nat
  p : Nat
  eb : Nat
  deriving DecidableEq, Repr, Inhabited

def f32 : Fmt := ⟨32, 24, 8⟩
def f64 : Fmt := ⟨64, 53, 11⟩

namespace Fmt

def fracBits (f : Fmt) : Nat := f.p - 1
def bias (f : Fmt) : Nat := 2 ^ (f.eb - 1) - 1
/-- Largest finite exponent (unbiased, of the leading bit). -/
def emax (f : Fmt) : Int := (bias f : Int)
/-- Smallest normal exponent (unbiased, of the leading bit). -/
def emin (f : Fmt) : Int := 1 - (bias f : Int)
/-- Exponent of the subnormal grid step `2^(emin-(p-1))`. -/
def gridExp (f : Fmt) : Int := emin f - ((f.p : Int) - 1)
def expMask (f : Fmt) : Nat := 2 ^ f.eb - 1
def signPart (f : Fmt) (s : Bool) : Nat := if s then 2 ^ (f.w - 1) else 0
/-- Infinity with the given sign. -/
def inf (f : Fmt) (s : Bool) : Nat := signPart f s ||| (expMask f <<< fracBits f)
/-- The canonical quiet NaN, positive: `0x7fc00000` / `0x7ff8000000000000`. -/
def qnan (f : Fmt) : Nat := (expMask f <<< fracBits f) ||| 2 ^ (f.p - 2)
/-- Zero with the given sign. -/
def zero (f : Fmt) (s : Bool) : Nat := signPart f s

def signBit (f : Fmt) (b : Nat) : Bool := (b / 2 ^ (f.w - 1)) % 2 = 1
def expField (f : Fmt) (b : Nat) : Nat := (b / 2 ^ fracBits f) % 2 ^ f.eb
def fracField (f : Fmt) (b : Nat) : Nat := b % 2 ^ fracBits f

def isNaN (f : Fmt) (b : Nat) : Bool := expField f b = expMask f && fracField f b ≠ 0
def isInf (f : Fmt) (b : Nat) : Bool := expField f b = expMask f && fracField f b = 0
def isZero (f : Fmt) (b : Nat) : Bool := expField f b = 0 && fracField f b = 0
/-- Subnormal, non-zero. -/
def isSub (f : Fmt) (b : Nat) : Bool := expField f b = 0 && fracField f b ≠ 0
def isFinite (f : Fmt) (b : Nat) : Bool := expField f b ≠ expMask f

/-- `(sign, significand, exponent)` of `b`, exact: `b = (-1)^sign · m · 2^e` for finite `b`
(with `m = 0` for both zeros). -/
def decode (f : Fmt) (b : Nat) : Bool × Nat × Int :=
  let s := signBit f b
  let ef := expField f b
  let fr := fracField f b
  if ef = 0 then (s, fr, gridExp f)
  else (s, 2 ^ fracBits f + fr, (ef : Int) - (bias f : Int) - (fracBits f : Int))

/-- Encode the value `q · 2^(eTop-(p-1))` when `q` has exactly `p` bits, or the overflow image
`2^p` already normalised by the caller (`eTop` then names the next binade). -/
def encodeNormal (f : Fmt) (s : Bool) (q : Nat) (eTop : Int) : Nat :=
  if eTop > emax f then inf f s
  else
    let ef := (eTop + (bias f : Int)).toNat
    signPart f s ||| (ef <<< fracBits f) ||| (q - 2 ^ (f.p - 1))

/-- Encode `r · 2^(gridExp f)` with `0 ≤ r ≤ 2^(p-1)` (subnormal, or the smallest normal). -/
def encodeSub (f : Fmt) (s : Bool) (r : Nat) : Nat :=
  if r = 0 then zero f s
  else if r < 2 ^ (f.p - 1) then signPart f s ||| r
  else encodeNormal f s r (emin f)

/-- Number of binary digits of `n` (fuel-bounded: every value formed in this module is below
`2^2200`, since `f64` exponents span about 2100 doublings). -/
def bitLenF : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else 1 + bitLenF fuel (n / 2)

def bitLen (n : Nat) : Nat := bitLenF 4096 n

/-- Round `(-1)^s · (m · 2^e + ε)`, `0 ≤ ε < 2^e` (a sticky bit below the last bit of `m`), to
`f`, round-to-nearest-ties-to-even. `m = 0` gives a signed zero. -/
def roundPackS (f : Fmt) (s : Bool) (m : Nat) (e : Int) (sticky : Bool) : Nat :=
  if m = 0 then zero f s
  else
    let bl := bitLen m
    let eTop := e + (bl : Int) - 1
    if eTop < emin f then
      -- gradual underflow: round onto the subnormal grid
      let ge := gridExp f
      if e ≥ ge then encodeSub f s (m <<< (e - ge).toNat)
      else
        let d := (ge - e).toNat
        let q := m >>> d
        let r := m % 2 ^ d
        let up := if r > 2 ^ (d - 1) then true
                  else if r < 2 ^ (d - 1) then false
                  else if sticky then true else q % 2 = 1
        encodeSub f s (if up then q + 1 else q)
    else
      let d := bl - f.p
      if d ≤ 0 then encodeNormal f s (m <<< (f.p - bl)) eTop
      else
        let q := m >>> d
        let r := m % 2 ^ d
        let up := if r > 2 ^ (d - 1) then true
                  else if r < 2 ^ (d - 1) then false
                  else if sticky then true else q % 2 = 1
        let q := if up then q + 1 else q
        if q = 2 ^ f.p then encodeNormal f s (2 ^ (f.p - 1)) (eTop + 1)
        else encodeNormal f s q eTop

def roundPack (f : Fmt) (s : Bool) (m : Nat) (e : Int) : Nat := roundPackS f s m e false

/-! ## Comparison of non-NaN values -/

/-- `|a| < |b|` for finite non-NaN `a`, `b` (either may be zero). -/
def magLt (f : Fmt) (a b : Nat) : Bool :=
  let (_, ma, ea) := decode f a
  let (_, mb, eb) := decode f b
  if ma = 0 then mb ≠ 0
  else if mb = 0 then false
  else
    let e := min ea eb
    (ma <<< (ea - e).toNat) < (mb <<< (eb - e).toNat)

def eqBits (f : Fmt) (a b : Nat) : Bool :=
  if isNaN f a || isNaN f b then false
  else if isZero f a && isZero f b then true
  else if signBit f a ≠ signBit f b then false
  else if isZero f a || isZero f b then false
  else
    let (_, ma, ea) := decode f a
    let (_, mb, eb) := decode f b
    let e := min ea eb
    (ma <<< (ea - e).toNat) = (mb <<< (eb - e).toNat)

def ltBits (f : Fmt) (a b : Nat) : Bool :=
  if isNaN f a || isNaN f b then false
  else if isZero f a && isZero f b then false
  else if signBit f a ≠ signBit f b then signBit f a
  else if signBit f a then magLt f b a
  else magLt f a b

/-! ## Arithmetic -/

def add (f : Fmt) (a b : Nat) : Nat :=
  if isNaN f a || isNaN f b then qnan f
  else if isInf f a && isInf f b then
    if signBit f a = signBit f b then inf f (signBit f a) else qnan f
  else if isInf f a then inf f (signBit f a)
  else if isInf f b then inf f (signBit f b)
  else
    let sa := signBit f a
    let sb := signBit f b
    let (_, ma, ea) := decode f a
    let (_, mb, eb) := decode f b
    if ma = 0 && mb = 0 then zero f (sa && sb)
    else
      let e := min ea eb
      let A : Int := (if sa then -1 else 1) * (((ma <<< (ea - e).toNat) : Nat) : Int)
      let B : Int := (if sb then -1 else 1) * (((mb <<< (eb - e).toNat) : Nat) : Int)
      let S := A + B
      if S = 0 then zero f false
      else roundPack f (S < 0) S.natAbs e

/-- The sign bit as `0`/`1` (the arithmetic form keeps the bit lemmas simple). -/
def signNat (f : Fmt) (b : Nat) : Nat := b / 2 ^ (f.w - 1) % 2

/-- Sign flip, as a bit operation: XOR with the sign bit. Bit-preserving for NaN payloads. -/
def neg (f : Fmt) (a : Nat) : Nat := (a ^^^ 2 ^ (f.w - 1)) % 2 ^ f.w

def abs (f : Fmt) (a : Nat) : Nat := a &&& (2 ^ (f.w - 1) - 1)

def copysign (f : Fmt) (a b : Nat) : Nat := abs f a + signNat f b * 2 ^ (f.w - 1)

def sub (f : Fmt) (a b : Nat) : Nat := add f a (neg f b)

def mul (f : Fmt) (a b : Nat) : Nat :=
  let sa := signBit f a
  let sb := signBit f b
  if isNaN f a || isNaN f b then qnan f
  else if (isInf f a && isZero f b) || (isZero f a && isInf f b) then qnan f
  else if isInf f a || isInf f b then inf f (sa ≠ sb)
  else if isZero f a || isZero f b then zero f (sa ≠ sb)
  else
    let (_, ma, ea) := decode f a
    let (_, mb, eb) := decode f b
    roundPack f (sa ≠ sb) (ma * mb) (ea + eb)

def div (f : Fmt) (a b : Nat) : Nat :=
  let sa := signBit f a
  let sb := signBit f b
  if isNaN f a || isNaN f b then qnan f
  else if (isInf f a && isInf f b) || (isZero f a && isZero f b) then qnan f
  else if isInf f a then inf f (sa ≠ sb)
  else if isInf f b then zero f (sa ≠ sb)
  else if isZero f b then inf f (sa ≠ sb)
  else if isZero f a then zero f (sa ≠ sb)
  else
    let (_, ma, ea) := decode f a
    let (_, mb, eb) := decode f b
    let ex := ea - eb
    let s := bitLen mb + f.p + 2 - bitLen ma
    let num := ma <<< s
    let q := num / mb
    let r := num % mb
    roundPackS f (sa ≠ sb) q (ex - (s : Int)) (r ≠ 0)

/-- `min`: NaN if either operand is; for equal values the bitwise OR of the operands, which merges
the sign bits (`min(+0,-0) = -0`). This is Winch's branchless sequence
(`cranelift-codegen-0.132.0/src/isa/x64/inst/emit.rs:783-880`): ordered-equal → `orps`,
unordered → add → canonicalised NaN, otherwise `minss`. -/
def min (f : Fmt) (a b : Nat) : Nat :=
  if isNaN f a || isNaN f b then qnan f
  else if eqBits f a b then a ||| b
  else if ltBits f a b then a else b

/-- `max`: as `min`, with the AND of equal values (`max(+0,-0) = +0`). -/
def max (f : Fmt) (a b : Nat) : Nat :=
  if isNaN f a || isNaN f b then qnan f
  else if eqBits f a b then a &&& b
  else if ltBits f a b then b else a

/-- Floor of the square root, by binary search downwards from `2^63` (every root here is
`< 2^58`; for f32/f64 the argument to `isqrt` below is `< 2^115`). -/
def isqrtGo (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, r => r
  | fuel + 1, bit, r =>
    if bit = 0 then r
    else if (r + bit) * (r + bit) ≤ n then isqrtGo n fuel (bit / 2) (r + bit)
    else isqrtGo n fuel (bit / 2) r

def isqrt (n : Nat) : Nat := isqrtGo n 64 (2 ^ 63) 0

def sqrt (f : Fmt) (a : Nat) : Nat :=
  if isNaN f a then qnan f
  else if isZero f a then a
  else if signBit f a then qnan f
  else if isInf f a then a
  else
    let (_, m, e) := decode f a
    -- write the value as `M · 2^E` with `E` even, then scale by `2^(2k)` for `p+4` root bits
    let M := if e % 2 = 0 then m else m * 2
    let E := if e % 2 = 0 then e else e - 1
    let k := if bitLen M ≥ 2 * (f.p + 4) then 0 else (2 * (f.p + 4) - bitLen M + 1) / 2
    let n := M <<< (2 * k)
    let s := isqrt n
    roundPackS f false s (E / 2 - (k : Int)) (s * s ≠ n)

/-! ## Rounding to an integer value (`ceil`, `floor`, `trunc`, `nearest`) -/

inductive RMode where
  | down | up | zero | nearest
  deriving DecidableEq, Repr, Inhabited

def roundToInt (f : Fmt) (md : RMode) (a : Nat) : Nat :=
  if isNaN f a then qnan f
  else if isInf f a || isZero f a then a
  else
    let s := signBit f a
    let (_, m, e) := decode f a
    if e ≥ 0 then a
    else
      let d := (-e).toNat
      let q := m >>> d
      let r := m % 2 ^ d
      let up := match md with
        | .down => s && r ≠ 0
        | .up => (!s) && r ≠ 0
        | .zero => false
        | .nearest =>
          if r > 2 ^ (d - 1) then true
          else if r < 2 ^ (d - 1) then false
          else q % 2 = 1
      let q := if up then q + 1 else q
      if q = 0 then zero f s else roundPack f s q 0

def ceil (f : Fmt) (a : Nat) : Nat := roundToInt f .up a
def floor (f : Fmt) (a : Nat) : Nat := roundToInt f .down a
def trunc (f : Fmt) (a : Nat) : Nat := roundToInt f .zero a
def nearest (f : Fmt) (a : Nat) : Nat := roundToInt f .nearest a

/-! ## Integer conversions -/

/-- Integer → float, round-to-nearest-ties-to-even (IEEE 754 §5.4.1). -/
def convertInt (f : Fmt) (n : Int) : Nat := roundPack f (n < 0) n.natAbs 0

/-- `trunc(x)` as an exact `Int`, or `none` when the conversion traps (NaN, infinity, or a
truncated value outside `[lo, hi]`). -/
def truncToInt (f : Fmt) (a : Nat) (lo hi : Int) : Option Int :=
  if isNaN f a || isInf f a then none
  else
    let s := signBit f a
    let (_, m, e) := decode f a
    let mag : Nat := if e ≥ 0 then m <<< e.toNat else m >>> (-e).toNat
    let v : Int := if s then -(mag : Int) else mag
    if lo ≤ v ∧ v ≤ hi then some v else none

/-- Saturating truncation: NaN → 0, otherwise clamp to `[lo, hi]` (Wasm `trunc_sat`). Returns the
two's-complement bit pattern of width `w`. -/
def truncSat (f : Fmt) (a : Nat) (lo hi : Int) (w : Nat) : Nat :=
  match truncToInt f a lo hi with
  | some v => (v % (2 ^ w : Int)).toNat
  | none => if isNaN f a then 0
            else if signBit f a then (lo % (2 ^ w : Int)).toNat
            else (hi % (2 ^ w : Int)).toNat

/-- Trapping truncation `i32/i64.trunc_f32/f64_s/u`: `none` is the `IllegalArithmetic` trap. -/
def truncTrapping (f : Fmt) (a : Nat) (lo hi : Int) (w : Nat) : Option Nat :=
  (truncToInt f a lo hi).map fun v => (v % (2 ^ w : Int)).toNat

/-- `f32.demote_f64`. NaN → canonical f32 NaN: Winch canonicalises after `demote`
(`visitor.rs:1156-1162`), so the f64 payload is discarded. -/
def demote (a : Nat) : Nat :=
  if isNaN f64 a then qnan f32
  else if isInf f64 a then inf f32 (signBit f64 a)
  else if isZero f64 a then zero f32 (signBit f64 a)
  else
    let (s, m, e) := decode f64 a
    roundPack f32 s m e

/-- `f64.promote_f32`. NaN → canonical f64 NaN (`visitor.rs:1164-1170`); every other value is
exactly representable. -/
def promote (a : Nat) : Nat :=
  if isNaN f32 a then qnan f64
  else if isInf f32 a then inf f64 (signBit f32 a)
  else if isZero f32 a then zero f64 (signBit f32 a)
  else
    let (s, m, e) := decode f32 a
    roundPack f64 s m e

end Fmt

/-! ## Opcode signatures and dispatch

Opcodes are the Wasm 1.0 numbers that `NearSpecV3.Wasm.Decode.isFloatOp` recognises. Loads
(`0x2A/0x2B`), stores (`0x38/0x39`) and constants (`0x43/0x44`) carry immediates and are handled by
the interpreter; everything in this section is a register/memory-stack operator with no immediate.
-/

/-- `true` for every float opcode this module decides (no immediates; loads, stores and `const`
are handled by the interpreter). -/
def isFloatOpNoImm (op : Nat) : Bool :=
  (0x5B ≤ op && op ≤ 0x66) || (0x8B ≤ op && op ≤ 0xA6) ||
  (0xA8 ≤ op && op ≤ 0xAB) || (0xAE ≤ op && op ≤ 0xB1) ||
  (0xB2 ≤ op && op ≤ 0xBF) || (0xFC00 ≤ op && op ≤ 0xFC07)

/-- Result value type of a float opcode (`i32`/`i64`/`f32`/`f64`). -/
def floatResultType (op : Nat) : VT :=
  if (0x5B ≤ op && op ≤ 0x66) then .i32
  else if (0x8B ≤ op && op ≤ 0x98) then .f32
  else if (0x99 ≤ op && op ≤ 0xA6) then .f64
  else if op ≤ 0xAB then .i32
  else if op ≤ 0xB1 then .i64
  else if op ≤ 0xB6 then .f32
  else if op ≤ 0xBB then .f64
  else if op = 0xBC then .i32
  else if op = 0xBD then .i64
  else if op = 0xBE then .f32
  else if op = 0xBF then .f64
  else if op ≤ 0xFC03 then .i32
  else .i64

/-- Operand types (0, 1 or 2) of a float opcode. -/
def floatOperands (op : Nat) : Array VT :=
  if (0x5B ≤ op && op ≤ 0x60) then #[.f32, .f32]
  else if (0x61 ≤ op && op ≤ 0x66) then #[.f64, .f64]
  else if (0x8B ≤ op && op ≤ 0x91) then #[.f32]
  else if (0x92 ≤ op && op ≤ 0x98) then #[.f32, .f32]
  else if (0x99 ≤ op && op ≤ 0x9F) then #[.f64]
  else if (0xA0 ≤ op && op ≤ 0xA6) then #[.f64, .f64]
  else if op ≤ 0xAB then (if op ≤ 0xA9 then #[.f32] else #[.f64])
  else if op ≤ 0xB1 then (if op ≤ 0xAF then #[.f32] else #[.f64])
  else if op ≤ 0xB6 then
    (if op ≤ 0xB3 then #[.i32] else if op ≤ 0xB5 then #[.i64] else #[.f64])
  else if op ≤ 0xBB then
    (if op ≤ 0xB8 then #[.i32] else if op ≤ 0xBA then #[.i64] else #[.f32])
  else if op = 0xBC then #[.f32]
  else if op = 0xBD then #[.f64]
  else if op = 0xBE then #[.i32]
  else if op = 0xBF then #[.i64]
  else if op ≤ 0xFC03 then (if op ≤ 0xFC01 then #[.f32] else #[.f64])
  else (if op ≤ 0xFC05 then #[.f32] else #[.f64])

/-- `true` for the eight trapping `trunc_f*` conversions (finite-wasm `cvtop_partial`: a gas `pre`
point rather than a `pure` point). -/
def floatPartial (op : Nat) : Bool := (0xA8 ≤ op && op ≤ 0xAB) || (0xAE ≤ op && op ≤ 0xB1)

/-- Two's-complement bounds of a conversion to a `w`-bit integer. -/
def intBounds (w : Nat) (signed : Bool) : Int × Int :=
  if signed then (-(2 ^ (w - 1) : Int), (2 ^ (w - 1) : Int) - 1)
  else (0, (2 ^ w : Int) - 1)

/-- One float operator on bit patterns. `a` is the first operand, `b` the second (unused by
unary operators); both are the raw bit patterns of the type `floatOperands` names. `none` is
a trap (`IllegalArithmetic`). -/
def evalFloatOp (op : Nat) : Nat → Nat → Option Nat :=
  fun a b =>
  match op with
  -- comparisons
  | 0x5B => some (Num.b2 (Fmt.eqBits f32 a b))
  | 0x5C => some (Num.b2 (!Fmt.eqBits f32 a b))
  | 0x5D => some (Num.b2 (Fmt.ltBits f32 a b))
  | 0x5E => some (Num.b2 (Fmt.ltBits f32 b a))
  | 0x5F => some (Num.b2 (Fmt.ltBits f32 a b || Fmt.eqBits f32 a b))
  | 0x60 => some (Num.b2 (Fmt.ltBits f32 b a || Fmt.eqBits f32 a b))
  | 0x61 => some (Num.b2 (Fmt.eqBits f64 a b))
  | 0x62 => some (Num.b2 (!Fmt.eqBits f64 a b))
  | 0x63 => some (Num.b2 (Fmt.ltBits f64 a b))
  | 0x64 => some (Num.b2 (Fmt.ltBits f64 b a))
  | 0x65 => some (Num.b2 (Fmt.ltBits f64 a b || Fmt.eqBits f64 a b))
  | 0x66 => some (Num.b2 (Fmt.ltBits f64 b a || Fmt.eqBits f64 a b))
  -- f32 arithmetic
  | 0x8B => some (Fmt.abs f32 a)
  | 0x8C => some (Fmt.neg f32 a)
  | 0x8D => some (Fmt.ceil f32 a)
  | 0x8E => some (Fmt.floor f32 a)
  | 0x8F => some (Fmt.trunc f32 a)
  | 0x90 => some (Fmt.nearest f32 a)
  | 0x91 => some (Fmt.sqrt f32 a)
  | 0x92 => some (Fmt.add f32 a b)
  | 0x93 => some (Fmt.sub f32 a b)
  | 0x94 => some (Fmt.mul f32 a b)
  | 0x95 => some (Fmt.div f32 a b)
  | 0x96 => some (Fmt.min f32 a b)
  | 0x97 => some (Fmt.max f32 a b)
  | 0x98 => some (Fmt.copysign f32 a b)
  -- f64 arithmetic
  | 0x99 => some (Fmt.abs f64 a)
  | 0x9A => some (Fmt.neg f64 a)
  | 0x9B => some (Fmt.ceil f64 a)
  | 0x9C => some (Fmt.floor f64 a)
  | 0x9D => some (Fmt.trunc f64 a)
  | 0x9E => some (Fmt.nearest f64 a)
  | 0x9F => some (Fmt.sqrt f64 a)
  | 0xA0 => some (Fmt.add f64 a b)
  | 0xA1 => some (Fmt.sub f64 a b)
  | 0xA2 => some (Fmt.mul f64 a b)
  | 0xA3 => some (Fmt.div f64 a b)
  | 0xA4 => some (Fmt.min f64 a b)
  | 0xA5 => some (Fmt.max f64 a b)
  | 0xA6 => some (Fmt.copysign f64 a b)
  -- trapping truncations
  | 0xA8 => Fmt.truncTrapping f32 a (intBounds 32 true).1 (intBounds 32 true).2 32
  | 0xA9 => Fmt.truncTrapping f32 a (intBounds 32 false).1 (intBounds 32 false).2 32
  | 0xAA => Fmt.truncTrapping f64 a (intBounds 32 true).1 (intBounds 32 true).2 32
  | 0xAB => Fmt.truncTrapping f64 a (intBounds 32 false).1 (intBounds 32 false).2 32
  | 0xAE => Fmt.truncTrapping f32 a (intBounds 64 true).1 (intBounds 64 true).2 64
  | 0xAF => Fmt.truncTrapping f32 a (intBounds 64 false).1 (intBounds 64 false).2 64
  | 0xB0 => Fmt.truncTrapping f64 a (intBounds 64 true).1 (intBounds 64 true).2 64
  | 0xB1 => Fmt.truncTrapping f64 a (intBounds 64 false).1 (intBounds 64 false).2 64
  -- complete conversions
  | 0xB2 => some (Fmt.convertInt f32 (Num.signed 32 a))
  | 0xB3 => some (Fmt.convertInt f32 (a : Int))
  | 0xB4 => some (Fmt.convertInt f32 (Num.signed 64 a))
  | 0xB5 => some (Fmt.convertInt f32 (a : Int))
  | 0xB6 => some (Fmt.demote a)
  | 0xB7 => some (Fmt.convertInt f64 (Num.signed 32 a))
  | 0xB8 => some (Fmt.convertInt f64 (a : Int))
  | 0xB9 => some (Fmt.convertInt f64 (Num.signed 64 a))
  | 0xBA => some (Fmt.convertInt f64 (a : Int))
  | 0xBB => some (Fmt.promote a)
  | 0xBC => some (a % 2 ^ 32)                          -- i32.reinterpret_f32
  | 0xBD => some (a % 2 ^ 64)                          -- i64.reinterpret_f64
  | 0xBE => some (a % 2 ^ 32)                          -- f32.reinterpret_i32
  | 0xBF => some (a % 2 ^ 64)                          -- f64.reinterpret_i64
  -- saturating truncations
  | 0xFC00 => some (Fmt.truncSat f32 a (intBounds 32 true).1 (intBounds 32 true).2 32)
  | 0xFC01 => some (Fmt.truncSat f32 a (intBounds 32 false).1 (intBounds 32 false).2 32)
  | 0xFC02 => some (Fmt.truncSat f64 a (intBounds 32 true).1 (intBounds 32 true).2 32)
  | 0xFC03 => some (Fmt.truncSat f64 a (intBounds 32 false).1 (intBounds 32 false).2 32)
  | 0xFC04 => some (Fmt.truncSat f32 a (intBounds 64 true).1 (intBounds 64 true).2 64)
  | 0xFC05 => some (Fmt.truncSat f32 a (intBounds 64 false).1 (intBounds 64 false).2 64)
  | 0xFC06 => some (Fmt.truncSat f64 a (intBounds 64 true).1 (intBounds 64 true).2 64)
  | 0xFC07 => some (Fmt.truncSat f64 a (intBounds 64 false).1 (intBounds 64 false).2 64)
  | _ => none

/-! ## The canonical-NaN boundary, stated exactly

The two claims that distinguish canonicalising from bit-preserving operators, as kernel-checked
facts about the bit patterns (not as prose). -/

/-- A canonicalising operator applied to a NaN operand yields the canonical NaN, whatever the
payload. -/
theorem add_nan_canonical_f32 (a b : Nat) (h : Fmt.isNaN f32 a) :
    Fmt.add f32 a b = Fmt.qnan f32 := by
  simp [Fmt.add, h]

theorem add_nan_canonical_f64 (a b : Nat) (h : Fmt.isNaN f64 a) :
    Fmt.add f64 a b = Fmt.qnan f64 := by
  simp [Fmt.add, h]

/-- The canonical NaN is exactly the pinned bit pattern. -/
theorem qnan_f32_bits : Fmt.qnan f32 = 0x7FC00000 := by decide
theorem qnan_f64_bits : Fmt.qnan f64 = 0x7FF8000000000000 := by decide

/-- A bit-preserving operator keeps the payload: `abs` clears exactly the sign bit. -/
theorem abs_f32_payload (a : Nat) : Fmt.abs f32 a = a &&& 0x7FFFFFFF := by
  simp [Fmt.abs, f32]

/-- `neg` flips exactly the sign bit, so a NaN keeps its payload and gets the other sign. -/
theorem neg_f32_payload (a : Nat) (h : a < 2 ^ 32) :
    Fmt.neg f32 a = a ^^^ 0x80000000 := by
  simp only [Fmt.neg, f32]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow h (by decide))

/-- `copysign` keeps the significand-and-exponent bits of its first operand: the NaN payload is
preserved and only the sign is taken from the second operand (Winch `float_copysign`,
`isa/x64/masm.rs:607-643`). -/
theorem copysign_f32_body (a b : Nat) :
    Fmt.copysign f32 a b % 2 ^ 31 = a % 2 ^ 31 := by
  have := Nat.mod_lt (a % 2 ^ 31) (show 0 < 2 ^ 31 by decide)
  have hb : b / 2 ^ 31 % 2 = 0 ∨ b / 2 ^ 31 % 2 = 1 := by omega
  simp only [Fmt.copysign, Fmt.abs, Fmt.signNat, f32, Nat.and_two_pow_sub_one_eq_mod]
  rcases hb with h | h <;> simp [h]

/-- `copysign` takes exactly the second operand's sign bit. -/
theorem copysign_f32_sign (a b : Nat) :
    Fmt.signNat f32 (Fmt.copysign f32 a b) = b / 2 ^ 31 % 2 := by
  have ha := Nat.mod_lt (a % 2 ^ 31) (show 0 < 2 ^ 31 by decide)
  have hb : b / 2 ^ 31 % 2 = 0 ∨ b / 2 ^ 31 % 2 = 1 := by omega
  simp only [Fmt.copysign, Fmt.abs, Fmt.signNat, f32, Nat.and_two_pow_sub_one_eq_mod]
  rcases hb with h | h <;> simp [h]

end NearSpecV3.Wasm
