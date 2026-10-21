import WasmBase.Prelude
import WasmBase.Local.Add
/-!
# WasmBase.ChiAir — the Keccak `chi` step as a standalone AIR

`results/pq-keccak-air/README.md` §1 corrects the record: Keccak-f[1600] has no multiplication, so a
64-bit-multiply gadget is *not* what it needs.  The only non-trivial step is `chi`,

```
A[x] = B[x] ^ ((~B[x+1]) & B[x+2])
```

on 64-bit lanes.  This file builds **just that** as a `WasmBase.Chips.Table`, and proves the bridge
to the spec's own `chi` (`NearSpecV3.Wasm.Crypto.keccakF`,
`spec/lean/v3/NearSpecV3/Wasm/Crypto.lean:50-53`).

## The construction: three lookups per byte, no row constraint

On bytes the spec's expression rewrites to *two AND/XOR steps* using the identity

```
(~b) & c = c ^ (c & b)          (byte-wise, because `~b` is `255 − b`)
```

so with `u = c & b` (BYTE kind 1) and `t = c ^ u`, `r = a ^ t` (BYTE kind 3 both times),

```
r = a ^ (c ^ (c & b))
```

is `a ^ ((~b) & c)` — the spec's `chi`, with **no NOT column and no negation constraint**.  A row is
therefore

* `a`, `b`, `c` — the three input lanes, 8 byte columns each;
* `u`, `t`, `r` — the two intermediates and the result, 8 byte columns each;

48 columns, **zero row constraints**, and 24 BYTE lookups (3 per byte position):

| lookup | meaning |
|---|---|
| `[1, b_i, c_i, u_i]` | kind 1 = AND: `u_i = b_i & c_i` |
| `[3, c_i, u_i, t_i]` | kind 3 = XOR: `t_i = c_i ^ u_i = (~b_i) & c_i` |
| `[3, a_i, t_i, r_i]` | kind 3 = XOR: `r_i = a_i ^ t_i` |

(These are the exact kinds `WasmBase/Chips.lean`'s `Byte` table answers, `Chips.lean:627-631`.)

Every byte value is pinned by a BYTE lookup: the table side of the bus only ever carries `x, y < 256`
(`WasmBase.Main.Lookups.byte_row_msgs`), so a matched query has byte operands and a byte answer.  That
is why the row needs no range constraints and attribute (degree) **0**.

## Why this is cheap, and why the old verdict was wrong

* **No 64-bit multiply, no MUL chip.**  `chi` is an AND and two XORs.  Even the NOT is gone.
* **No 64-bit comparison, no field negation, no range gadget.**  Everything is a byte lookup.
* **Max degree 0**; the widest message is 4 fields (BYTE's own), which is the narrowest message in the
  base layer.
* The old claim — "needs a 64-bit-multiply gadget", "degree ≥ 9" — was an artefact of trying to keep
  the lanes in 16-bit limbs and multiply.  The base layer is **byte-sliced** (`BIT`, `BYTE`, `SHIFT`),
  and in that representation `chi` is two bit-ops.

## Soundness

`chi_sound` takes a row's natural-number cells and its 24 BYTE answers and concludes

```
val8 r = val8 a ^^^ ((2^64 − 1 − val8 b) &&& val8 c)
```

which is `val8 a ^^^ ((~~~ val8 b) &&& val8 c)` in `Nat` (`airChi_eq_specChi`).  `ChiVectors.lean`
then checks the generated row against the spec's own `chi` on edge and pseudo-random vectors, and
checks that every lookup it issues is one the `BYTE` table answers.
-/
namespace WasmBase
namespace Chips
namespace Chi

set_option linter.unusedSimpArgs false
open Expr

/-! ## Column layout -/

/-- 8 byte columns, `n0 … n7`. -/
def byteNames (p : String) : List String := (List.range 8).map fun i => p ++ toString i

def aB : Nat := 0    -- 0..7   lane a
def bB : Nat := 8    -- 8..15  lane b
def cB : Nat := 16   -- 16..23 lane c
def uB : Nat := 24   -- 24..31 `c & b`
def tB : Nat := 32   -- 32..39 `c ^ (c & b)` = `(~b) & c`
def rB : Nat := 40   -- 40..47 lane r (the result)
def ncols : Nat := 48

def cols : List String := byteNames "a" ++ byteNames "b" ++ byteNames "c" ++ byteNames "u" ++
  byteNames "t" ++ byteNames "r"

/-- Activity count of a row: no instruction selector, no state transition, so a row is always
active. -/
def act : Expr := 1

/-- The row environment the `CHI` table is evaluated in: it reads no `nxt`, no public input and no
selector, so all three are `0`. -/
def emptyRow : Row := ⟨fun _ => 0, fun _ => 0, fun _ => 0, false, false⟩

/-! ## No row constraints; 24 BYTE lookups -/

/-- The `CHI` table has **no polynomial constraints**: every relation is a BYTE lookup. -/
def constraints : List Expr := []

/-- Three BYTE lookups per byte position — `(1, b, c, u)`, `(3, c, u, t)`, `(3, a, t, r)` — each
with count 1 (a row is one `chi` application). -/
def inters : List Inter :=
  (List.range 8).flatMap (fun i =>
    [byteQ 1 (v (bB + i)) (v (cB + i)) (v (uB + i)) act,
     byteQ 3 (v (cB + i)) (v (uB + i)) (v (tB + i)) act,
     byteQ 3 (v (aB + i)) (v (tB + i)) (v (rB + i)) act])

def table : Table := ⟨"CHI", cols, constraints, inters⟩

theorem ncols_eq : ncols = 48 := rfl
theorem inters_len : inters.length = 24 := by decide
theorem constraints_len : constraints.length = 0 := rfl

/-- With no constraints there is nothing above degree 0. -/
theorem constraints_degree : constraints.all (fun e => e.degree ≤ 2) = true := rfl

/-- The widest message is 4 fields, so `len + 1 = 5 ≤ 128` (`log_max_message_length = 7`). -/
theorem inters_msg_len : inters.all (fun i => i.msg.length ≤ 4) = true := by decide

/-! ## The lane-level `chi`

`val8` is `WasmBase.val8` (little-endian byte packing, `Prelude.lean:73`). -/

/-- Little-endian byte packing of a lane, `Σ 256^i · b_i`. -/
abbrev laneVal (b : Nat → Nat) : Nat := val8 b

/-- Eight bytes pack into a 64-bit lane value. -/
theorem laneVal_lt (b : Nat → Nat) (hb : ∀ i, i < 8 → b i < 256) : laneVal b < 2 ^ 64 := by
  have h0 := hb 0 (by decide); have h1 := hb 1 (by decide); have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide); have h4 := hb 4 (by decide); have h5 := hb 5 (by decide)
  have h6 := hb 6 (by decide); have h7 := hb 7 (by decide)
  simp only [laneVal, val8]
  omega

/-- **The `chi` identity at lane level**: `(~b) & c = c ^ (c & b)`.  This is what turns the spec's
`~~~`/`&&&`/`^^^` into the two AND/XOR lookups the row performs; `~~~b` is `2^64 − 1 − b` and
`(2^64 − 1 − b).testBit i = !b.testBit i` on `i < 64`. -/
theorem and_not (b c : Nat) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    (2 ^ 64 - 1 - b) &&& c = c ^^^ (c &&& b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_and]
  have e : 2 ^ 64 - 1 - b = 2 ^ 64 - (b + 1) := by omega
  by_cases h64 : i < 64
  · rw [e, Nat.testBit_two_pow_sub_succ (by omega)]
    simp [h64]; cases b.testBit i <;> cases c.testBit i <;> rfl
  · have hi : 64 ≤ i := by omega
    have hle : 2 ^ 64 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
    have hb2 : b.testBit i = false := Nat.testBit_lt_two_pow (by omega)
    have hc2 : c.testBit i = false := Nat.testBit_lt_two_pow (by omega)
    have hlt : (2 ^ 64 - 1 - b).testBit i = false := by
      rw [e, Nat.testBit_two_pow_sub_succ (by omega)]
      simp [h64]
    simp [hb2, hc2, hlt]

/-- **Soundness of one `CHI` row.**  From the 24 BYTE answers — every byte below 256,
`u = b & c`, `t = c ^ u`, `r = a ^ t` — the result lane is the lane-level
`a ^ (~b & c)` of the three input lanes. -/
theorem chi_sound (c : Nat → Nat)
    (hlk : ∀ i, i < 8 →
      c (aB + i) < 256 ∧ c (bB + i) < 256 ∧ c (cB + i) < 256 ∧
      c (uB + i) = c (bB + i) &&& c (cB + i) ∧
      c (tB + i) = c (cB + i) ^^^ c (uB + i) ∧
      c (rB + i) = c (aB + i) ^^^ c (tB + i)) :
    laneVal (fun i => c (rB + i)) =
      laneVal (fun i => c (aB + i)) ^^^
        ((2 ^ 64 - 1 - laneVal (fun i => c (bB + i))) &&& laneVal (fun i => c (cB + i))) := by
  have haa : ∀ i, i < 8 → c (aB + i) < 256 := fun i hi => (hlk i hi).1
  have hbb : ∀ i, i < 8 → c (bB + i) < 256 := fun i hi => (hlk i hi).2.1
  have hcc : ∀ i, i < 8 → c (cB + i) < 256 := fun i hi => (hlk i hi).2.2.1
  have huu : ∀ i, i < 8 → c (uB + i) < 256 := fun i hi =>
    (hlk i hi).2.2.2.1 ▸ and_byte (by have := hbb i hi; simpa using this)
  have htt : ∀ i, i < 8 → c (tB + i) < 256 := fun i hi =>
    (hlk i hi).2.2.2.2.1 ▸ xor_byte (by have := hcc i hi; simpa using this)
      (by have := huu i hi; simpa using this)
  -- `val8 u = val8 b &&& val8 c`
  have hu : laneVal (fun i => c (uB + i)) = laneVal (fun i => c (bB + i)) &&& laneVal (fun i => c (cB + i)) := by
    have hrun : ∀ k, k < 8 → c (uB + k) = c (bB + k) &&& c (cB + k) := fun k hk => (hlk k hk).2.2.2.1
    have hlt : ∀ k, k < 8 → c (bB + k) &&& c (cB + k) < 256 := fun k hk =>
      and_byte (by have := hbb k hk; simpa using this)
    exact (val8_byteop (· && ·) (· &&& ·) (fun x y i => Nat.testBit_and x y i)
      (fun i => c (bB + i)) (fun i => c (cB + i)) (fun i => c (uB + i))
      (fun k hk => by have := hbb k hk; simpa using this)
      (fun k hk => by have := hcc k hk; simpa using this)
      hrun hlt).symm
  -- `val8 t = val8 c ^^^ val8 u`
  have ht : laneVal (fun i => c (tB + i)) = laneVal (fun i => c (cB + i)) ^^^ laneVal (fun i => c (uB + i)) := by
    have hrun : ∀ k, k < 8 → c (tB + k) = c (cB + k) ^^^ c (uB + k) := fun k hk => (hlk k hk).2.2.2.2.1
    have hlt : ∀ k, k < 8 → c (cB + k) ^^^ c (uB + k) < 256 := fun k hk =>
      xor_byte (by have := hcc k hk; simpa using this) (by have := huu k hk; simpa using this)
    exact (val8_byteop (fun a b => a ^^ b) (· ^^^ ·) (fun x y i => Nat.testBit_xor x y i)
      (fun i => c (cB + i)) (fun i => c (uB + i)) (fun i => c (tB + i))
      (fun k hk => by have := hcc k hk; simpa using this)
      (fun k hk => by have := huu k hk; simpa using this)
      hrun hlt).symm
  -- `val8 r = val8 a ^^^ val8 t`
  have hr : laneVal (fun i => c (rB + i)) = laneVal (fun i => c (aB + i)) ^^^ laneVal (fun i => c (tB + i)) := by
    have hrun : ∀ k, k < 8 → c (rB + k) = c (aB + k) ^^^ c (tB + k) := fun k hk => (hlk k hk).2.2.2.2.2
    have hlt : ∀ k, k < 8 → c (aB + k) ^^^ c (tB + k) < 256 := fun k hk =>
      xor_byte (by have := haa k hk; simpa using this) (by have := htt k hk; simpa using this)
    exact (val8_byteop (fun a b => a ^^ b) (· ^^^ ·) (fun x y i => Nat.testBit_xor x y i)
      (fun i => c (aB + i)) (fun i => c (tB + i)) (fun i => c (rB + i))
      (fun k hk => by have := haa k hk; simpa using this)
      (fun k hk => by have := htt k hk; simpa using this)
      hrun hlt).symm
  rw [hr, ht, hu, Nat.and_comm (laneVal (fun i => c (bB + i))),
    and_not (laneVal (fun i => c (bB + i))) (laneVal (fun i => c (cB + i)))
    (laneVal_lt _ (fun i hi => hbb i hi)) (laneVal_lt _ (fun i hi => hcc i hi))]

end Chi
end Chips
end WasmBase
