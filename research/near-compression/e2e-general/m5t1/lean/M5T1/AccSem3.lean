import M5T1.AccSem2

/-!
# M5T1.AccSem3 — `ACC`'s byte ranges, and bytes ↔ words (F-4)

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.AccSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.AccDef M5T1.RbSem M5T1.BndLay

section
open M5T1.Acc
def I1 : List Interaction := comp (c "act") (c "cid") (hW ++ blockW ++ oW)
def I2 : List Interaction := [rcv B_ACCD (c "lst") [c "hid"]]
def I3 : List Interaction := (List.range 128).map fun j => rcv B_RNG (c "act") [c "blk" j]
def I4 : List Interaction := (List.range 16).flatMap (splitRng (c "act") blkS)
def I5 : List Interaction := (List.range 48).map fun j => rcv B_RNG (c "lst") [c "dg" j]
def I6 : List Interaction := (List.range 6).flatMap (splitRng (c "lst") dgS)
theorem ix_eq : Acc.table.interactions = I1 ++ I2 ++ I3 ++ I4 ++ I5 ++ I6 := rfl
end

theorem mi1 {i : Interaction} (h : i ∈ I1) : i ∈ Acc.table.interactions := by
  rw [ix_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl h))))
theorem mi3 {i : Interaction} (h : i ∈ I3) : i ∈ Acc.table.interactions := by
  rw [ix_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inr h)))
theorem mi4 {i : Interaction} (h : i ∈ I4) : i ∈ Acc.table.interactions := by
  rw [ix_eq]; simp only [List.mem_append]; exact .inl (.inl (.inr h))
theorem mi5 {i : Interaction} (h : i ∈ I5) : i ∈ Acc.table.interactions := by
  rw [ix_eq]; simp only [List.mem_append]; exact .inl (.inr h)
theorem mi6 {i : Interaction} (h : i ∈ I6) : i ∈ Acc.table.interactions := by
  rw [ix_eq]; simp only [List.mem_append]; exact .inr h

section
variable {tape xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (fullAir tape xtape) pub tr)
  (hr1 : NoRng tape) (hr2 : NoRng xtape)
include H hr1 hr2

/-- A gated `RNG` receive of `ACC` with its gate at `1` reads a byte. -/
theorem rngA {r : Nat} (hr : r < tr.height 7) {g e : Expr} (hi : rcv B_RNG g [e] ∈ Acc.table.interactions)
    (hg : ev tr 7 r pub g = 1) : ev tr 7 r pub e < 256 := by
  have hge : g.eval tr 7 r pub = 1 := by
    have := eval_of_ev (e := g) (t := 7) (r := r) hg (by decide)
    rw [this]; rfl
  exact rng_recv H hr1 hr2 (acc_lt (tape := tape) (xtape := xtape)) hr hi rfl rfl
    (by rw [multNat_one hge]; decide) rfl

/-- **The bytes and splits of an active row's block.** -/
theorem blk_ranges {r : Nat} (hr : r < tr.height 7) (ha : accC tr r "act" = 1) :
    (∀ j < 128, accC tr r "blk" j < 256) ∧
    ∀ w < 16, accC tr r "bsp" (4 * w) < 32 ∧ accC tr r "bsp" (4 * w + 1) < 8 ∧
      accC tr r "bsp" (4 * w + 2) < 4 ∧ accC tr r "bsp" (4 * w + 3) < 64 := by
  have hg : ev tr 7 r pub (Acc.c "act") = 1 := by rw [evAc, ha]
  refine ⟨fun j hj => ?_, fun w hw => ?_⟩
  · have := rngA H hr1 hr2 hr (mi3 (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)) hg
    rwa [evAc] at this
  · have mem : ∀ i ∈ Acc.splitRng (Acc.c "act") Acc.blkS w, i ∈ Acc.table.interactions :=
      fun i hi => mi4 (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, hi⟩)
    have q : ∀ (k m : Nat), m ≤ 64 →
        rcv B_RNG (Acc.c "act") [Acc.blkS (4 * w + k)] ∈ Acc.splitRng (Acc.c "act") Acc.blkS w →
        rcv B_RNG (Acc.c "act") [K m * Acc.blkS (4 * w + k)] ∈ Acc.splitRng (Acc.c "act") Acc.blkS w →
        accC tr r "bsp" (4 * w + k) < 256 ∧ m * accC tr r "bsp" (4 * w + k) < 256 := by
      intro k m hm64 h1 h2
      have e1 := rngA H hr1 hr2 hr (mem _ h1) hg
      have e2 := rngA H hr1 hr2 hr (mem _ h2) hg
      simp only [evMul, evK, Acc.blkS, evAc] at e1 e2
      rw [Nat.mod_eq_of_lt (show m < 2013265921 by omega),
        Nat.mod_eq_of_lt (show m * accC tr r "bsp" (4 * w + k) < 2013265921 by
          have := Nat.mul_le_mul (show m ≤ 64 from hm64) (Nat.le_of_lt e1); omega)] at e2
      exact ⟨e1, e2⟩
    obtain ⟨a0, b0⟩ := q 0 8 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a1, b1⟩ := q 1 32 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a2, b2⟩ := q 2 64 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a3, b3⟩ := q 3 4 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    simp only [Nat.add_zero] at a0 b0
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The bytes and splits of a last row's digest.** -/
theorem dg_ranges {r : Nat} (hr : r < tr.height 7) (ha : accC tr r "lst" = 1) :
    (∀ j < 48, accC tr r "dg" j < 256) ∧
    ∀ w < 6, accC tr r "dsp" (4 * w) < 32 ∧ accC tr r "dsp" (4 * w + 1) < 8 ∧
      accC tr r "dsp" (4 * w + 2) < 4 ∧ accC tr r "dsp" (4 * w + 3) < 64 := by
  have hg : ev tr 7 r pub (Acc.c "lst") = 1 := by rw [evAc, ha]
  refine ⟨fun j hj => ?_, fun w hw => ?_⟩
  · have := rngA H hr1 hr2 hr (mi5 (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)) hg
    rwa [evAc] at this
  · have mem : ∀ i ∈ Acc.splitRng (Acc.c "lst") Acc.dgS w, i ∈ Acc.table.interactions :=
      fun i hi => mi6 (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, hi⟩)
    have q : ∀ (k m : Nat), m ≤ 64 →
        rcv B_RNG (Acc.c "lst") [Acc.dgS (4 * w + k)] ∈ Acc.splitRng (Acc.c "lst") Acc.dgS w →
        rcv B_RNG (Acc.c "lst") [K m * Acc.dgS (4 * w + k)] ∈ Acc.splitRng (Acc.c "lst") Acc.dgS w →
        accC tr r "dsp" (4 * w + k) < 256 ∧ m * accC tr r "dsp" (4 * w + k) < 256 := by
      intro k m hm64 h1 h2
      have e1 := rngA H hr1 hr2 hr (mem _ h1) hg
      have e2 := rngA H hr1 hr2 hr (mem _ h2) hg
      simp only [evMul, evK, Acc.dgS, evAc] at e1 e2
      rw [Nat.mod_eq_of_lt (show m < 2013265921 by omega),
        Nat.mod_eq_of_lt (show m * accC tr r "dsp" (4 * w + k) < 2013265921 by
          have := Nat.mul_le_mul (show m ≤ 64 from hm64) (Nat.le_of_lt e1); omega)] at e2
      exact ⟨e1, e2⟩
    obtain ⟨a0, b0⟩ := q 0 8 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a1, b1⟩ := q 1 32 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a2, b2⟩ := q 2 64 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a3, b3⟩ := q 3 4 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    simp only [Nat.add_zero] at a0 b0
    refine ⟨by omega, by omega, by omega, by omega⟩

end

/-! ## Bytes ↔ words -/

/-- **A word from its chip limbs and its 8 big-endian bytes** (`Acc.wordOf`'s limb formulas with the
splits `b₅ = s₀ + 32 s₁`, `b₂ = s₂ + 4 s₃`). -/
theorem word_bytes {x : Nat} (hx : x < 2 ^ 64) (b : Nat → Nat) (s0 s1 s2 s3 : Nat)
    (hb : ∀ i < 8, b i < 256) (h0 : s0 < 32) (h1 : s1 < 8) (h2 : s2 < 4) (h3 : s3 < 64)
    (e2 : b 5 = s0 + 32 * s1) (e5 : b 2 = s2 + 4 * s3)
    (hl : Acc.wlimbs x = [b 7 + 256 * b 6 + 65536 * s0, s1 + 8 * b 4 + 2048 * b 3 + 524288 * s2,
      s3 + 64 * b 1 + 16384 * b 0]) :
    ∀ i < 8, x / 256 ^ (7 - i) % 256 = b i := by
  simp only [Acc.wlimbs, List.cons.injEq, and_true] at hl
  obtain ⟨l0, l1, l2⟩ := hl
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide); have b2 := hb 2 (by decide)
  have b3 := hb 3 (by decide); have b4 := hb 4 (by decide); have b5 := hb 5 (by decide)
  have b6 := hb 6 (by decide); have b7 := hb 7 (by decide)
  have hxv : x = b 7 + 256 * b 6 + 65536 * b 5 + 16777216 * b 4 + 4294967296 * b 3 +
      1099511627776 * b 2 + 281474976710656 * b 1 + 72057594037927936 * b 0 := by omega
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reducePow] <;> omega

end M5T1.AccSem
