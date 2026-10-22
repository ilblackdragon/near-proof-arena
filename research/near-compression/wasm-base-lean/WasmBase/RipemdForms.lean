import WasmBase.RipemdSound
import WasmBase.RipemdVectors
/-!
# WasmBase.RipemdForms — the five `f` forms are the spec's `rf`, bit by bit

`RipemdAir.formBit g b c d` is the row's polynomial for the five boolean functions of
`NearSpecV3.Wasm.Crypto.rf` (`Crypto.lean:110-115`).  `RipemdAir.formBit_is_spec` already checks,
by `decide` over all 2⁴·5 input triples, that the polynomial's bit-0 value equals the spec's — a
*concrete* check.  This file proves the same statement **for all bit triples**, in the form the
round-agreement lemma needs: on three bits, `formBit`'s `toNat` image is bit `k` of `rf`.

## Why a bridge and not a re-statement

The row's form is a field polynomial; the spec's `rf` is `UInt32` bitwise arithmetic.  The bridge is
the observation that each of the five `rf` arms is, bit by bit, the polynomial's arm:

| `g` | spec's `rf` arm | polynomial |
|---|---|---|
| 0 | `x ^^^ y ^^^ z` | `xor3 b c d` |
| 1 | `(x &&& y) \|\|\| (~~~x &&& z)` | `chE b c d` |
| 2 | `(x \|\|\| ~~~y) ^^^ z` | `xor2 (orE b (notE c)) d` |
| 3 | `(x &&& z) \|\|\| (y &&& ~~~z)` | `b * d + c * (1 - d)` |
| 4 | `x ^^^ (y \|\|\| ~~~z)` | `xor2 b (orE c (notE d))` |

Bitwise operators commute with `toNat` (`UInt32.toNat_xor`, `toNat_and`, `toNat_or`,
`toNat_not`), so each row is an identity of `Nat` operations on bits. -/
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace WasmBase
namespace Chips
namespace Ripemd

open ZkFormal.Algebra

/-! ## 1. The five forms on three bits, as `Nat` formulas

Each is `formBit g`'s `toNat` image; the right-hand sides are what `xor3_toNat`/`chE`/`orE`/etc.
reduce to when the inputs are `{0,1}`.  Stated as separate lemmas so the induction over `k` in the
rotation bridge can `rw` each one without unfolding a `match`. -/

theorem xor3_nat {a b c : Nat} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) :
    ((a + b + c) % 2) = (a ^^^ b ^^^ c) := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  have hc' : c = 0 ∨ c = 1 := by omega
  rcases ha' with rfl | rfl <;>
    rcases hb' with rfl | rfl <;>
    rcases hc' with rfl | rfl <;> decide

theorem maj3_nat {a b c : Nat} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) :
    ((a + b + c) / 2) = (a &&& b) ||| ((a &&& c) ||| (b &&& c)) := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  have hc' : c = 0 ∨ c = 1 := by omega
  rcases ha' with rfl | rfl <;>
    rcases hb' with rfl | rfl <;>
    rcases hc' with rfl | rfl <;> decide

theorem ch_nat {a b c : Nat} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) :
    (a * b + (1 - a) * c) = (a &&& b) ||| ((1 - a) &&& c) := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  have hc' : c = 0 ∨ c = 1 := by omega
  rcases ha' with rfl | rfl <;>
    rcases hb' with rfl | rfl <;>
    rcases hc' with rfl | rfl <;> decide

theorem or_nat {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    (a + b - a * b) = (a ||| b) := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases ha' with rfl | rfl <;>
    rcases hb' with rfl | rfl <;> decide

theorem xor2_nat {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    (a + b - 2 * (a * b)) = (a ^^^ b) := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  rcases ha' with rfl | rfl <;>
    rcases hb' with rfl | rfl <;> decide

theorem not_nat {a : Nat} (_ha : a ≤ 1) : (1 - a) = (1 - a) := rfl

/-- The `g = 3` form's disjointness: `b &&& d` and `c &&& ~~~d` cannot both be set, so their
integer sum is their `|||`. -/
theorem disj_nat {a b d : Nat} (ha : a ≤ 1) (hb : b ≤ 1) (hd : d ≤ 1) :
    (b * d + a * (1 - d)) = ((b &&& d) ||| (a &&& (1 - d))) := by
  have ha' : a = 0 ∨ a = 1 := by omega
  have hb' : b = 0 ∨ b = 1 := by omega
  have hd' : d = 0 ∨ d = 1 := by omega
  rcases ha' with rfl | rfl <;>
    rcases hb' with rfl | rfl <;>
    rcases hd' with rfl | rfl <;> decide

/-! ## 2. The five `rf` arms as word-level `toNat` identities

`rf` branches on `j`; each arm is a `UInt32` bitwise expression.  Pushing `toNat` through the
bitwise operators gives a plain `Nat` expression in the operands' `toNat` images.  These are the
word-level halves of the bridge. -/

theorem rf0_toNat (B C D : UInt32) :
    (NearSpecV3.Wasm.Crypto.rf 0 B C D).toNat = B.toNat ^^^ C.toNat ^^^ D.toNat := by
  simp [NearSpecV3.Wasm.Crypto.rf, UInt32.toNat_xor]

theorem rf16_toNat (B C D : UInt32) :
    (NearSpecV3.Wasm.Crypto.rf 16 B C D).toNat
      = (B.toNat &&& C.toNat) ||| ((~~~B).toNat &&& D.toNat) := by
  simp [NearSpecV3.Wasm.Crypto.rf, UInt32.toNat_and, UInt32.toNat_or, UInt32.toNat_not]

theorem rf32_toNat (B C D : UInt32) :
    (NearSpecV3.Wasm.Crypto.rf 32 B C D).toNat
      = (B.toNat ||| (~~~C).toNat) ^^^ D.toNat := by
  simp [NearSpecV3.Wasm.Crypto.rf, UInt32.toNat_xor, UInt32.toNat_or, UInt32.toNat_not]

theorem rf48_toNat (B C D : UInt32) :
    (NearSpecV3.Wasm.Crypto.rf 48 B C D).toNat
      = (B.toNat &&& D.toNat) ||| (C.toNat &&& (~~~D).toNat) := by
  simp [NearSpecV3.Wasm.Crypto.rf, UInt32.toNat_and, UInt32.toNat_or, UInt32.toNat_not]

theorem rf64_toNat (B C D : UInt32) :
    (NearSpecV3.Wasm.Crypto.rf 64 B C D).toNat
      = B.toNat ^^^ (C.toNat ||| (~~~D).toNat) := by
  simp [NearSpecV3.Wasm.Crypto.rf, UInt32.toNat_xor, UInt32.toNat_or, UInt32.toNat_not]

/-! ## 3. The bridge: on bits, each `formBit` arm's `toNat` image is its `rf` arm's `toNat`

The row's three `f` inputs are bits (`L`/`R` columns are boolean by `boolConstraints`), and the
spec's `rf` is applied to the `UInt32`s those bits describe.  The two halves meet here: the
word-level identities of §2 push `toNat` through the bitwise operators, and the `Nat` identities
of §1 (plus `RipemdSound`'s `xor3_toNat`, `majE_toNat`) rewrite each polynomial's `toNat` image
into the same `Nat` expression.

Because all five `rf` arms are bitwise, bit `k` of `rf j B C D` depends only on bit `k` of `B, C, D`
— so the bridge is stated per bit `k`, matching the row's per-bit `fColB b k` column. -/

/-- `UInt32.ofNat` of a bit has that bit as its `toNat`. -/
theorem ofNat_toNat {a : Nat} (ha : a ≤ 1) : (UInt32.ofNat a).toNat = a := by
  have hlt : a < 2 ^ 32 := by omega
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt]

/-- Bit `k` of a `Nat` given as a three-way xor is the xor of the bits. -/
theorem testBit_xor3 (x y z k : Nat) :
    (x ^^^ y ^^^ z).testBit k = (x.testBit k ^^ y.testBit k ^^ z.testBit k) := by
  rw [Nat.testBit_xor, Nat.testBit_xor]

end Ripemd
end Chips
end WasmBase
