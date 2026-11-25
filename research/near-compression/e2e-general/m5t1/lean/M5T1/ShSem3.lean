import M5T1.ShSem2
import M5T1.PubBytes

/-!
# M5T1.ShSem3 — `SH`'s byte ranges (F-7)

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.ShSem

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.ShDef
open M5T1.AccSem (evAdd evMul evSub evK evOne evZero evFirst0 evFirstS evTrans evPub gate_eq
  bool_le)

section
open M5T1.Sh
def I1 : List Interaction := Acc.comp (c "act") (c "cid") (hW ++ blockW ++ oW)
def I2 : List Interaction := [rcv B_SHD (c "lst") ([c "hid", c "fx", c "bi"] ++ dgLimbs),
   rcv B_SHB (c "act" * c "fx") (c "hid" :: c "bi" :: limbs43 blkB)]
def I3 : List Interaction := (List.range 128).map fun j => rcv B_RNG (c "act") [c "blk" j]
def I4 : List Interaction := (List.range 16).flatMap (Acc.splitRng (c "act") blkS)
def I5 : List Interaction := (List.range 48).map fun j => rcv B_RNG (c "lst") [c "dg" j]
def I6 : List Interaction := (List.range 6).flatMap (Acc.splitRng (c "lst") dgS)
theorem ix_eq : Sh.table.interactions = I1 ++ I2 ++ I3 ++ I4 ++ I5 ++ I6 := rfl
end

theorem mi1 {i : Interaction} (h : i ∈ I1) : i ∈ Sh.table.interactions := by
  rw [ix_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl h))))
theorem mi3 {i : Interaction} (h : i ∈ I3) : i ∈ Sh.table.interactions := by
  rw [ix_eq]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inr h)))
theorem mi4 {i : Interaction} (h : i ∈ I4) : i ∈ Sh.table.interactions := by
  rw [ix_eq]; simp only [List.mem_append]; exact .inl (.inl (.inr h))
theorem mi5 {i : Interaction} (h : i ∈ I5) : i ∈ Sh.table.interactions := by
  rw [ix_eq]; simp only [List.mem_append]; exact .inl (.inr h)
theorem mi6 {i : Interaction} (h : i ∈ I6) : i ∈ Sh.table.interactions := by
  rw [ix_eq]; simp only [List.mem_append]; exact .inr h

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
  (hr2 : NoRng xtape)
include H hr2

/-- A gated `RNG` receive of table `t` with its gate at `1` reads a byte. -/
theorem rngT {t r : Nat} (ht : t < (Se.fullSe xtape).tables.length) (hr : r < tr.height t) {g e : Expr}
    (hi : rcv B_RNG g [e] ∈ ((Se.fullSe xtape).tables[t]'ht).interactions)
    (hg : ev tr t r pub g = 1) : ev tr t r pub e < 256 := by
  have hge : g.eval tr t r pub = 1 := by
    have := eval_of_ev (e := g) (t := t) (r := r) hg (by decide)
    rw [this]; rfl
  exact PubBytes.rng_recv_gen H (PubBytes.se_rngAir hr2) ht hr hi rfl rfl
    (by rw [multNat_one hge]; decide) rfl

theorem rngS {r : Nat} (hr : r < tr.height 2) {g e : Expr} (hi : rcv B_RNG g [e] ∈ Sh.table.interactions)
    (hg : ev tr 2 r pub g = 1) : ev tr 2 r pub e < 256 :=
  rngT H hr2 (t := 2) sh_lt hr hi hg

/-- **The bytes and splits of an active row's block.** -/
theorem blk_ranges {r : Nat} (hr : r < tr.height 2) (ha : shC tr r "act" = 1) :
    (∀ j < 128, shC tr r "blk" j < 256) ∧
    ∀ w < 16, shC tr r "bsp" (4 * w) < 32 ∧ shC tr r "bsp" (4 * w + 1) < 8 ∧
      shC tr r "bsp" (4 * w + 2) < 4 ∧ shC tr r "bsp" (4 * w + 3) < 64 := by
  have hg : ev tr 2 r pub (Sh.c "act") = 1 := by rw [evSc, ha]
  refine ⟨fun j hj => ?_, fun w hw => ?_⟩
  · have := rngS H hr2 hr (mi3 (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)) hg
    rwa [evSc] at this
  · have mem : ∀ i ∈ Acc.splitRng (Sh.c "act") Sh.blkS w, i ∈ Sh.table.interactions :=
      fun i hi => mi4 (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, hi⟩)
    have q : ∀ (k m : Nat), m ≤ 64 →
        rcv B_RNG (Sh.c "act") [Sh.blkS (4 * w + k)] ∈ Acc.splitRng (Sh.c "act") Sh.blkS w →
        rcv B_RNG (Sh.c "act") [K m * Sh.blkS (4 * w + k)] ∈ Acc.splitRng (Sh.c "act") Sh.blkS w →
        shC tr r "bsp" (4 * w + k) < 256 ∧ m * shC tr r "bsp" (4 * w + k) < 256 := by
      intro k m hm64 h1 h2
      have e1 := rngS H hr2 hr (mem _ h1) hg
      have e2 := rngS H hr2 hr (mem _ h2) hg
      simp only [evMul, evK, Sh.blkS, evSc] at e1 e2
      rw [Nat.mod_eq_of_lt (show m < 2013265921 by omega),
        Nat.mod_eq_of_lt (show m * shC tr r "bsp" (4 * w + k) < 2013265921 by
          have := Nat.mul_le_mul (show m ≤ 64 from hm64) (Nat.le_of_lt e1); omega)] at e2
      exact ⟨e1, e2⟩
    obtain ⟨a0, b0⟩ := q 0 8 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a1, b1⟩ := q 1 32 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a2, b2⟩ := q 2 64 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a3, b3⟩ := q 3 4 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    simp only [Nat.add_zero] at a0 b0
    refine ⟨by omega, by omega, by omega, by omega⟩

/-- **The bytes and splits of a last row's digest.** -/
theorem dg_ranges {r : Nat} (hr : r < tr.height 2) (ha : shC tr r "lst" = 1) :
    (∀ j < 48, shC tr r "dg" j < 256) ∧
    ∀ w < 6, shC tr r "dsp" (4 * w) < 32 ∧ shC tr r "dsp" (4 * w + 1) < 8 ∧
      shC tr r "dsp" (4 * w + 2) < 4 ∧ shC tr r "dsp" (4 * w + 3) < 64 := by
  have hg : ev tr 2 r pub (Sh.c "lst") = 1 := by rw [evSc, ha]
  refine ⟨fun j hj => ?_, fun w hw => ?_⟩
  · have := rngS H hr2 hr (mi5 (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)) hg
    rwa [evSc] at this
  · have mem : ∀ i ∈ Acc.splitRng (Sh.c "lst") Sh.dgS w, i ∈ Sh.table.interactions :=
      fun i hi => mi6 (List.mem_flatMap.2 ⟨w, List.mem_range.2 hw, hi⟩)
    have q : ∀ (k m : Nat), m ≤ 64 →
        rcv B_RNG (Sh.c "lst") [Sh.dgS (4 * w + k)] ∈ Acc.splitRng (Sh.c "lst") Sh.dgS w →
        rcv B_RNG (Sh.c "lst") [K m * Sh.dgS (4 * w + k)] ∈ Acc.splitRng (Sh.c "lst") Sh.dgS w →
        shC tr r "dsp" (4 * w + k) < 256 ∧ m * shC tr r "dsp" (4 * w + k) < 256 := by
      intro k m hm64 h1 h2
      have e1 := rngS H hr2 hr (mem _ h1) hg
      have e2 := rngS H hr2 hr (mem _ h2) hg
      simp only [evMul, evK, Sh.dgS, evSc] at e1 e2
      rw [Nat.mod_eq_of_lt (show m < 2013265921 by omega),
        Nat.mod_eq_of_lt (show m * shC tr r "dsp" (4 * w + k) < 2013265921 by
          have := Nat.mul_le_mul (show m ≤ 64 from hm64) (Nat.le_of_lt e1); omega)] at e2
      exact ⟨e1, e2⟩
    obtain ⟨a0, b0⟩ := q 0 8 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a1, b1⟩ := q 1 32 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a2, b2⟩ := q 2 64 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    obtain ⟨a3, b3⟩ := q 3 4 (by decide) (by simp [Acc.splitRng]) (by simp [Acc.splitRng])
    simp only [Nat.add_zero] at a0 b0
    refine ⟨by omega, by omega, by omega, by omega⟩

end

end M5T1.ShSem
