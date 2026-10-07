import ZkFormal.NearV3.Render.Ups.GMemCarry
import ZkFormal.NearV3.Render.Ups.MemRegisters

/-! New/old value-length register initialization, shifts and persistence. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cMemLengths : List Expr := UpsV3.cMem.drop 11

set_option hygiene false in
macro "mem_lengths_cases" : tactic => `(tactic| (
  change ex ∈ [UpsV3.cMem.getD 11 (Dsl.k 0),
    UpsV3.cMem.getD 12 (Dsl.k 0),
    UpsV3.cMem.getD 13 (Dsl.k 0),
    UpsV3.cMem.getD 14 (Dsl.k 0),
    UpsV3.cMem.getD 15 (Dsl.k 0),
    UpsV3.cMem.getD 16 (Dsl.k 0),
    UpsV3.cMem.getD 17 (Dsl.k 0),
    UpsV3.cMem.getD 18 (Dsl.k 0),
    UpsV3.cMem.getD 19 (Dsl.k 0),
    UpsV3.cMem.getD 20 (Dsl.k 0),
    UpsV3.cMem.getD 21 (Dsl.k 0),
    UpsV3.cMem.getD 22 (Dsl.k 0),
    UpsV3.cMem.getD 23 (Dsl.k 0),
    UpsV3.cMem.getD 24 (Dsl.k 0),
    UpsV3.cMem.getD 25 (Dsl.k 0),
    UpsV3.cMem.getD 26 (Dsl.k 0),
    UpsV3.cMem.getD 27 (Dsl.k 0),
    UpsV3.cMem.getD 28 (Dsl.k 0)] at hex
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))

set_option hygiene false in
macro "mem_lengths_eval" : tactic => `(tactic| (
  intro ex hex
  mem_lengths_cases <;> apply cast0 <;>
    ups_ev [UpsV3.cMem, UpsV3.Lb, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Nat.reduceMod, hC,hD] <;>
    (try cellsimp) <;> clear hC hD))

/-- Length-register behavior follows solely from the field cursor and scalar widths. -/
theorem mem_lengths_pair {C D P : Nat → Int} {fst lst trn : Int}
    {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u st' ix' fl' wi' u' : Nat}
    (hC : ∀ x, x < 187 → C x = QC I Q k p st ix fl wi u x)
    (hD : ∀ x, x < 187 → D x = QC I Q k (p + 1) st' ix' fl' wi' u' x)
    (hi : ix < fl) (h4 : st = 4 → fl = 4) (h8 : st = 8 → fl = 8)
    (hn : if ix + 1 < fl then st' = st ∧ ix' = ix + 1 else ix' = 0) :
    ∀ ex ∈ cMemLengths, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  mem_lengths_eval
  all_goals (
    by_cases hs4 : st = 4
    · subst st
      have hf : fl = 4 := h4 rfl
      subst fl
      rcases (show ix = 0 ∨ ix = 1 ∨ ix = 2 ∨ ix = 3 by omega) with rfl | rfl | rfl | rfl
      all_goals simp only [Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false] at hn
      all_goals try (obtain ⟨rfl,rfl⟩ := hn)
      all_goals try subst ix'
      all_goals simp_all [ind, Lb, slb, Int.add_right_neg]
    · by_cases hs8 : st = 8
      · subst st
        have hf : fl = 8 := h8 rfl
        subst fl
        rcases (show ix = 0 ∨ ix = 1 ∨ ix = 2 ∨ ix = 3 ∨ ix = 4 ∨ ix = 5 ∨ ix = 6 ∨ ix = 7 by omega)
          with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp only [Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false] at hn
        all_goals try (obtain ⟨rfl,rfl⟩ := hn)
        all_goals try subst ix'
        all_goals simp_all [ind, Lb, slb, Int.add_right_neg]
      · split at hn
        · obtain ⟨rfl,rfl⟩ := hn
          simp_all [ind, Lb, slb, Int.add_right_neg]
        · subst ix'
          by_cases hs'4 : st' = 4 <;> by_cases hs'8 : st' = 8 <;> simp_all [ind, Lb, slb, Int.add_right_neg]
  )

end UpsGen
end ZkFormal.NearV3.Render
