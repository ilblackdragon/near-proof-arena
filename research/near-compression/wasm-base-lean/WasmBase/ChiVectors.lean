import WasmBase.ChiAir
import NearSpecV3.Wasm.Crypto
/-!
# WasmBase.ChiVectors — the `CHI` table against the spec's own `chi`, with the kernel in the loop

`ChiAir.chi_sound` proves that a `CHI` row's result lane is the lane-level `a ^ (~b & c)` of its three
input lanes.  This file closes the other half — that this *is* the spec's `chi` — in three steps:

1. **`specChiNat`** is the spec's `chi` line (`NearSpecV3.Wasm.Crypto.keccakF`,
   `spec/lean/v3/NearSpecV3/Wasm/Crypto.lean:52-53`) evaluated on three lanes: literally
   `A ^^^ ((~~~ B) &&& C)` on `UInt64`s, with the arguments and the result moved through `Nat` so the
   kernel can `decide` on it.  **It is the spec's expression, not a restatement of the AIR.**
2. **A trace generator** (`genRow`): given the three lanes' natural values, it fills the 48 cells the
   row needs — bytes of `a`, `b`, `c`, `u`, `t`, `r` — computed from `Nat` bit operations, not from
   the spec's `UInt64`s.
3. **The differential test**: for edge vectors (all-zero, all-ones, alternating, single-bit,
   byte-pattern) and a set of pseudo-random 64-bit constants, the lane read back out of the generated
   row's `r` bytes equals `specChiNat` on the same lanes.  `decide` closes every case.

`genRow_byte` also checks that every one of the generator's 24 lookups is a message the `BYTE` table
answers, so the generated row is not an empty formalism: its lookups are answerable.
-/
set_option maxRecDepth 1000000

namespace WasmBase
namespace Chips
namespace Chi

open NearSpecV3.Wasm.Crypto
open WasmBase.Local

/-! ## `chi` on one lane triple: the spec's expression, and the row's expression -/

/-- **The spec's `chi`**, as `NearSpecV3.Wasm.Crypto.keccakF` computes it at `Crypto.lean:52-53`:
`A ^^^ ((~~~ B) &&& C)` on `UInt64` lanes. -/
def specChi (a b c : UInt64) : UInt64 := a ^^^ ((~~~ b) &&& c)

/-- The spec's `chi` on `Nat` lanes, through `UInt64`.  This is the form the differential test
compares against: the lane arithmetic is the spec's, only the representation is `Nat`. -/
def specChiNat (a b c : Nat) : Nat :=
  (specChi (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofNat c)).toNat

/-- The row's expression: `a ^ ((2^64 − 1 − b) & c)`, the natural-value image of `~~~`. -/
def airChi (a b c : Nat) : Nat := a ^^^ ((2 ^ 64 - 1 - b) &&& c)

/-- **The two spellings agree on 64-bit lanes.**  `~~~` is `2^64 − 1 − ·` on `Nat`
(`UInt64.toNat_not`), `&&&`/`^^^` commute with `toNat` (`UInt64.toNat_and`, `UInt64.toNat_xor`), and
`UInt64.ofNat x = x` for `x < 2^64` (`UInt64.toNat_ofNat`). -/
theorem airChi_eq_specChiNat (a b c : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    airChi a b c = specChiNat a b c := by
  have ea : (UInt64.ofNat a).toNat = a := by simp [Nat.mod_eq_of_lt ha]
  have eb : (UInt64.ofNat b).toNat = b := by simp [Nat.mod_eq_of_lt hb]
  have ec : (UInt64.ofNat c).toNat = c := by simp [Nat.mod_eq_of_lt hc]
  simp only [airChi, specChiNat, specChi, UInt64.toNat_xor, UInt64.toNat_and, UInt64.toNat_not, ea, eb, ec]

/-! ## The bytes of a lane -/

/-- Byte `i < 8` of a 64-bit lane, little-endian (the spec's sponge packs byte `k` of a block into
bits `8k..8k+7` of a lane, `Crypto.lean:70-73`). -/
def byteOf (x i : Nat) : Nat := x >>> (8 * i) % 2 ^ 8

theorem byteOf_lt (x i : Nat) : byteOf x i < 256 := by
  have : (2 : Nat) ^ 8 = 256 := rfl
  simp only [byteOf, this]; exact Nat.mod_lt _ (by decide)

theorem byteOf_xor (x y i : Nat) : byteOf (x ^^^ y) i = byteOf x i ^^^ byteOf y i := by
  simp only [byteOf]
  rw [Nat.shiftRight_xor_distrib, Nat.xor_mod_two_pow]

theorem byteOf_and (x y i : Nat) : byteOf (x &&& y) i = byteOf x i &&& byteOf y i := by
  simp only [byteOf]
  rw [Nat.shiftRight_and_distrib, Nat.and_mod_two_pow]

/-- A 64-bit lane is the little-endian packing of its eight bytes. -/
theorem val8_byteOf {x : Nat} (hx : x < 2 ^ 64) : val8 (fun i => byteOf x i) = x := by
  simp only [val8, byteOf]
  have h : ∀ i, x >>> (8 * i) % 256 = x / 2 ^ (8 * i) % 256 := by
    intro i; rw [Nat.shiftRight_eq_div_pow]
  simp only [h]
  omega

/-! ## The trace generator

`genRow a b c : Nat → Nat` is the 48-cell row for the triple `(a, b, c)`, `a, b, c < 2^64`:

| columns | value |
|---|---|
| `aB + i` | `byteOf a i` |
| `bB + i` | `byteOf b i` |
| `cB + i` | `byteOf c i` |
| `uB + i` | `byteOf b i &&& byteOf c i` (the kind-1 BYTE answer) |
| `tB + i` | `byteOf c i ^^^ byteOf u i` (the first kind-3 answer) |
| `rB + i` | `byteOf a i ^^^ byteOf t i` (the second kind-3 answer) |

Columns it does not mention are `0`. -/
def genRow (a b c : Nat) : Nat → Nat := fun j =>
  if j < 8 then byteOf a j
  else if j < 16 then byteOf b (j - 8)
  else if j < 24 then byteOf c (j - 16)
  else if j < 32 then byteOf b (j - 24) &&& byteOf c (j - 24)
  else if j < 40 then byteOf c (j - 32) ^^^ (byteOf b (j - 32) &&& byteOf c (j - 32))
  else if j < 48 then byteOf a (j - 40) ^^^
    (byteOf c (j - 40) ^^^ (byteOf b (j - 40) &&& byteOf c (j - 40)))
  else 0

/-! ### The generator's row, column by column -/

theorem genRow_a_aux (a b c i : Nat) (hi : i < 8) : genRow a b c i = byteOf a i := by
  have : i < 8 := hi
  simp only [genRow]
  rw [if_pos this]

theorem genRow_a (a b c i : Nat) (hi : i < 8) : genRow a b c (aB + i) = byteOf a i := by
  have e : aB + i = i := by simp only [aB]; omega
  rw [e, genRow_a_aux a b c i hi]

theorem genRow_b (a b c i : Nat) (hi : i < 8) : genRow a b c (8 + i) = byteOf b i := by
  have h1 : ¬ 8 + i < 8 := by omega
  have h2 : 8 + i < 16 := by omega
  simp only [genRow]
  rw [if_neg h1, if_pos h2]
  congr 1
  omega

theorem genRow_c (a b c i : Nat) (hi : i < 8) : genRow a b c (16 + i) = byteOf c i := by
  have h1 : ¬ 16 + i < 8 := by omega
  have h2 : ¬ 16 + i < 16 := by omega
  have h3 : 16 + i < 24 := by omega
  simp only [genRow]
  rw [if_neg h1, if_neg h2, if_pos h3]
  congr 1
  omega

theorem genRow_u (a b c i : Nat) (hi : i < 8) :
    genRow a b c (24 + i) = byteOf b i &&& byteOf c i := by
  have h1 : ¬ 24 + i < 8 := by omega
  have h2 : ¬ 24 + i < 16 := by omega
  have h3 : ¬ 24 + i < 24 := by omega
  have h4 : 24 + i < 32 := by omega
  simp only [genRow]
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
  have e1 : 24 + i - 24 = i := by omega
  rw [e1]

theorem genRow_t (a b c i : Nat) (hi : i < 8) :
    genRow a b c (32 + i) = byteOf c i ^^^ (byteOf b i &&& byteOf c i) := by
  have h1 : ¬ 32 + i < 8 := by omega
  have h2 : ¬ 32 + i < 16 := by omega
  have h3 : ¬ 32 + i < 24 := by omega
  have h4 : ¬ 32 + i < 32 := by omega
  have h5 : 32 + i < 40 := by omega
  simp only [genRow]
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
  have e1 : 32 + i - 32 = i := by omega
  rw [e1]

theorem genRow_r (a b c i : Nat) (hi : i < 8) :
    genRow a b c (40 + i) =
      byteOf a i ^^^ (byteOf c i ^^^ (byteOf b i &&& byteOf c i)) := by
  have h1 : ¬ 40 + i < 8 := by omega
  have h2 : ¬ 40 + i < 16 := by omega
  have h3 : ¬ 40 + i < 24 := by omega
  have h4 : ¬ 40 + i < 32 := by omega
  have h5 : ¬ 40 + i < 40 := by omega
  have h6 : 40 + i < 48 := by omega
  simp only [genRow]
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h6]
  have e1 : 40 + i - 40 = i := by omega
  rw [e1]

/-! ### The generator's row satisfies `chi_sound`'s hypotheses -/

theorem genRow_hlk_num (a b c : Nat) :
    ∀ i, i < 8 →
      genRow a b c i < 256 ∧ genRow a b c (8 + i) < 256 ∧
      genRow a b c (16 + i) < 256 ∧
      genRow a b c (24 + i) = genRow a b c (8 + i) &&& genRow a b c (16 + i) ∧
      genRow a b c (32 + i) = genRow a b c (16 + i) ^^^ genRow a b c (24 + i) ∧
      genRow a b c (40 + i) = genRow a b c i ^^^ genRow a b c (32 + i) := by
  intro i hi
  have ha := genRow_a_aux a b c i hi
  have hb := genRow_b a b c i hi
  have hc := genRow_c a b c i hi
  have hu := genRow_u a b c i hi
  have ht := genRow_t a b c i hi
  have hr := genRow_r a b c i hi
  refine ⟨ha ▸ byteOf_lt a i, hb ▸ byteOf_lt b i, hc ▸ byteOf_lt c i, ?_, ?_, ?_⟩
  · simp only [hb, hc, hu]
  · simp only [hc, hu, ht]
  · simp only [hr, ht, hu, ha]

/-- The same, in the row's own column names (`aB + i`, `bB + i`, …). -/
theorem genRow_hlk (a b c : Nat) :
    ∀ i, i < 8 →
      genRow a b c (aB + i) < 256 ∧ genRow a b c (bB + i) < 256 ∧
      genRow a b c (cB + i) < 256 ∧
      genRow a b c (uB + i) = genRow a b c (bB + i) &&& genRow a b c (cB + i) ∧
      genRow a b c (tB + i) = genRow a b c (cB + i) ^^^ genRow a b c (uB + i) ∧
      genRow a b c (rB + i) = genRow a b c (aB + i) ^^^ genRow a b c (tB + i) := by
  intro i hi
  have h := genRow_hlk_num a b c i hi
  simpa only [aB, bB, cB, uB, tB, rB, Nat.zero_add] using h

/-- The `genRow` lanes are the byte lanes read at the eight byte positions (`val8` looks at exactly
those). -/
theorem lane_a (a b c : Nat) :
    laneVal (fun i => genRow a b c (aB + i)) = laneVal (fun i => byteOf a i) := by
  have e : (fun i => genRow a b c (aB + i)) = (fun i => genRow a b c i) := by
    funext i; simp only [aB, Nat.zero_add]
  rw [e]
  simp only [laneVal, val8, genRow_a_aux a b c 0 (by decide), genRow_a_aux a b c 1 (by decide),
    genRow_a_aux a b c 2 (by decide), genRow_a_aux a b c 3 (by decide),
    genRow_a_aux a b c 4 (by decide), genRow_a_aux a b c 5 (by decide),
    genRow_a_aux a b c 6 (by decide), genRow_a_aux a b c 7 (by decide)]

theorem lane_b (a b c : Nat) :
    laneVal (fun i => genRow a b c (bB + i)) = laneVal (fun i => byteOf b i) := by
  simp only [laneVal, val8, bB, genRow_b a b c 0 (by decide), genRow_b a b c 1 (by decide),
    genRow_b a b c 2 (by decide), genRow_b a b c 3 (by decide), genRow_b a b c 4 (by decide),
    genRow_b a b c 5 (by decide), genRow_b a b c 6 (by decide), genRow_b a b c 7 (by decide)]

theorem lane_c (a b c : Nat) :
    laneVal (fun i => genRow a b c (cB + i)) = laneVal (fun i => byteOf c i) := by
  simp only [laneVal, val8, cB, genRow_c a b c 0 (by decide), genRow_c a b c 1 (by decide),
    genRow_c a b c 2 (by decide), genRow_c a b c 3 (by decide), genRow_c a b c 4 (by decide),
    genRow_c a b c 5 (by decide), genRow_c a b c 6 (by decide), genRow_c a b c 7 (by decide)]

/-- **`chi_sound` applied to the generated row**: the row's `r` lane is `airChi` of the inputs. -/
theorem genRow_chi (a b c : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    laneVal (fun i => genRow a b c (rB + i)) = airChi a b c := by
  have h := chi_sound (genRow a b c) (genRow_hlk a b c)
  have ha' := val8_byteOf ha
  have hb' := val8_byteOf hb
  have hc' := val8_byteOf hc
  rw [h, lane_a, lane_b, lane_c]
  simp only [laneVal] at ha' hb' hc' ⊢
  rw [ha', hb', hc']
  rfl

/-- The generator's `r` lane, read through the AIR's own layout, is the spec's `chi`. -/
theorem genRow_spec (a b c : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    laneVal (fun i => genRow a b c (rB + i)) = specChiNat a b c := by
  rw [genRow_chi a b c ha hb hc, airChi_eq_specChiNat a b c ha hb hc]

/-! ### The lookups the generator issues -/

/-- The `BYTE` table's answer for kind 1 is AND. -/
theorem byteF_one (x y : Nat) : byteF 1 x y = x &&& y := rfl
/-- kind 3 is XOR. -/
theorem byteF_three (x y : Nat) : byteF 3 x y = x ^^^ y := rfl

/-- Every message the generated row sends is a message the `BYTE` table answers
(`Byte.inters`, `Chips.lean:627-631`): 3 per byte position, 24 in total. -/
theorem genRow_byte (a b c : Nat) :
    ∀ i ∈ inters,
      (i.bus = busByte ∧ ∃ k x y, k < 4 ∧ x < 256 ∧ y < 256 ∧
        i.msg.map (·.eval (natRow (genRow a b c) emptyRow)) =
          [((k : Nat) : ZkFormal.Algebra.Fp), ((x : Nat) : ZkFormal.Algebra.Fp),
           ((y : Nat) : ZkFormal.Algebra.Fp), ((byteF k x y : Nat) : ZkFormal.Algebra.Fp)]) := by
  intro i hi
  simp only [inters, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
    List.mem_nil_iff, or_false] at hi
  rcases hi with ⟨j, hj, rfl | rfl | rfl⟩
  · -- kind 1: AND, `[1, b_j, c_j, b_j & c_j]`
    have hb := byteOf_lt b j
    have hc := byteOf_lt c j
    refine ⟨rfl, 1, genRow a b c (8 + j), genRow a b c (16 + j), by decide, ?_, ?_, ?_⟩
    · rw [genRow_b a b c j hj]; exact hb
    · rw [genRow_c a b c j hj]; exact hc
    · simp only [byteQ, byteF_one, List.map_cons, List.map_nil, natRow, emptyRow, Expr.eval_col,
        Expr.eval_ofNat', v, genRow_b a b c j hj, genRow_c a b c j hj, genRow_u a b c j hj,
        bB, cB, uB]
  · -- kind 3: `t = c ^ u`, `[3, c_j, u_j, c_j ^ u_j]`
    have hb := byteOf_lt b j
    have hc := byteOf_lt c j
    have hu := genRow_u a b c j hj
    have hcl := genRow_c a b c j hj
    refine ⟨rfl, 3, genRow a b c (16 + j), genRow a b c (24 + j), by decide, ?_, ?_, ?_⟩
    · rw [hcl]; exact hc
    · rw [hu]; exact and_byte (by omega)
    · simp only [byteQ, byteF_three, List.map_cons, List.map_nil, natRow, emptyRow, Expr.eval_col,
        Expr.eval_ofNat', v, hcl, hu, genRow_t a b c j hj, cB, uB, tB]
  · -- kind 3: `r = a ^ t`, `[3, a_j, t_j, a_j ^ t_j]`
    have ha := byteOf_lt a j
    have hb := byteOf_lt b j
    have hc := byteOf_lt c j
    have hu := genRow_u a b c j hj
    have ht := genRow_t a b c j hj
    have hal := genRow_a_aux a b c j hj
    refine ⟨rfl, 3, genRow a b c j, genRow a b c (32 + j), by decide, ?_, ?_, ?_⟩
    · rw [hal]; exact ha
    · rw [ht]; exact xor_byte (by omega) (and_byte (by omega))
    · simp only [byteQ, byteF_three, List.map_cons, List.map_nil, natRow, emptyRow, Expr.eval_col,
        Expr.eval_ofNat', v, hal, ht, genRow_r a b c j hj, aB, tB, rB, Nat.zero_add]

/-! ## The differential test

Edge vectors first — the cases a byte-sliced implementation gets wrong when it forgets that `~~~` is
lane-wide — then a set of pseudo-random-looking 64-bit constants.  Each case compares the lane read
out of the **generated row** against **`specChiNat`**, i.e. the spec's `A ^^^ ((~~~ B) &&& C)`. -/

-- all-zero
example : laneVal (fun i => genRow 0 0 0 (rB + i)) = specChiNat 0 0 0 := by decide
-- all-ones
example : laneVal (fun i => genRow (2^64-1) (2^64-1) (2^64-1) (rB + i)) =
    specChiNat (2^64-1) (2^64-1) (2^64-1) := by decide
-- alternating lanes, both phases
example : laneVal (fun i => genRow 0xAAAAAAAAAAAAAAAA 0x5555555555555555 0xAAAAAAAAAAAAAAAA (rB + i)) =
    specChiNat 0xAAAAAAAAAAAAAAAA 0x5555555555555555 0xAAAAAAAAAAAAAAAA := by decide
example : laneVal (fun i => genRow 0x5555555555555555 0xAAAAAAAAAAAAAAAA 0x5555555555555555 (rB + i)) =
    specChiNat 0x5555555555555555 0xAAAAAAAAAAAAAAAA 0x5555555555555555 := by decide
-- single bits, low and high
example : laneVal (fun i => genRow 1 1 1 (rB + i)) = specChiNat 1 1 1 := by decide
example : laneVal (fun i => genRow (2^63) 1 0 (rB + i)) = specChiNat (2^63) 1 0 := by decide
example : laneVal (fun i => genRow 1 (2^63) (2^63) (rB + i)) = specChiNat 1 (2^63) (2^63) := by decide
-- top bit of every byte
example : laneVal (fun i => genRow 0x8080808080808080 0x8080808080808080 0x8080808080808080 (rB + i)) =
    specChiNat 0x8080808080808080 0x8080808080808080 0x8080808080808080 := by decide
-- a byte stamp: eight distinct bytes per lane
example : laneVal (fun i => genRow 0x0706050403020100 0x0F0E0D0C0B0A0908 0x1716151413121110 (rB + i)) =
    specChiNat 0x0706050403020100 0x0F0E0D0C0B0A0908 0x1716151413121110 := by decide
-- pseudo-random-looking 64-bit constants
example : laneVal (fun i => genRow 0x0123456789ABCDEF 0xFEDCBA9876543210 0x0F0F0F0F0F0F0F0F (rB + i)) =
    specChiNat 0x0123456789ABCDEF 0xFEDCBA9876543210 0x0F0F0F0F0F0F0F0F := by decide
example : laneVal (fun i => genRow 0xDEADBEEFCAFEBABE 0x1337133713371337 0xB16B00B5DEADC0DE (rB + i)) =
    specChiNat 0xDEADBEEFCAFEBABE 0x1337133713371337 0xB16B00B5DEADC0DE := by decide
example : laneVal (fun i => genRow 0x9E3779B97F4A7C15 0xCBF29CE484222325 0x100000001B3 (rB + i)) =
    specChiNat 0x9E3779B97F4A7C15 0xCBF29CE484222325 0x100000001B3 := by decide
example : laneVal (fun i => genRow 0xFFFFFFFF00000000 0x00000000FFFFFFFF 0xFF00FF00FF00FF00 (rB + i)) =
    specChiNat 0xFFFFFFFF00000000 0x00000000FFFFFFFF 0xFF00FF00FF00FF00 := by decide
example : laneVal (fun i => genRow 0x00000000000000FF 0xFF00000000000000 0x00FF00FF00FF00FF (rB + i)) =
    specChiNat 0x00000000000000FF 0xFF00000000000000 0x00FF00FF00FF00FF := by decide
example : laneVal (fun i => genRow 0x8000000000000001 0x1 0x8000000000000000 (rB + i)) =
    specChiNat 0x8000000000000001 0x1 0x8000000000000000 := by decide
-- the spec's own round constant, as lane 0
example : laneVal (fun i => genRow 0x0000000000008082 0x800000000000808A 0x8000000080008000 (rB + i)) =
    specChiNat 0x0000000000008082 0x800000000000808A 0x8000000080008000 := by decide

/-- **The differential test, closed form**: the same comparison over a vector list. -/
theorem chi_diff :
    ([(0, 0, 0), (1, 1, 1), (0x0123456789ABCDEF, 0xFEDCBA9876543210, 0x0F0F0F0F0F0F0F0F),
      (0xDEADBEEFCAFEBABE, 0x1337133713371337, 0xB16B00B5DEADC0DE)]).all
      (fun v => laneVal (fun i => genRow v.1 v.2.1 v.2.2 (rB + i)) =
        specChiNat v.1 v.2.1 v.2.2) = true := by decide

end Chi
end Chips
end WasmBase
