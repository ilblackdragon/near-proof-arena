import ZkFormal.NearV3.Render.Ups.GBool
import ZkFormal.NearV3.Render.Ups.FieldFacts

/-! Serialization frame of `cFields`.  The remaining successor and window-role constraints
are not included in this theorem. -/
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

/-- One-hot field state, initial tag/start, and zero index at every field start. -/
def cFieldFrame : List Expr := UpsV3.cFields.take 4

theorem fields_frame_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (ok : FieldsOk Q) (hp : p < Q.q.length)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cFieldFrame, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  change ex ∈ [sub (sumc states) (c qb),
    .mul (c pf) (.mul (c qb) (Dsl.not (c sTAG))),
    .mul (c pf) (.mul (c qb) (Dsl.not (c fs))), .mul (c fs) (c idx)] at hex
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl
  · have hs := ok.state hp
    generalize fieldAt Q.shape p = fa at hC hs
    obtain ⟨st,ix,fl,wi⟩ := fa
    have hcases : st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 ∨ st = 4 ∨ st = 5 ∨ st = 6 ∨ st = 7 ∨ st = 8 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply cast0 <;> ups_ev [hC] <;> cellsimp <;> simp [ind]
  · apply cast0; ups_ev [hC]; cellsimp
    by_cases h : p = 0
    · subst p; rw [ok.first]; simp [ind]
    · simp [ind, h]
  · apply cast0; ups_ev [hC]; cellsimp
    by_cases h : p = 0
    · subst p; rw [ok.first]; simp [ind]
    · simp [ind, h]
  · apply cast0; ups_ev [hC]; cellsimp
    simp only [ind]; split <;> simp_all

/-- The field frame holds on the complete padded update trace.  This is an explicit
subgroup result; it does not assert the still-open `cFields` successor/window constraints. -/
theorem cFieldFrame_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cFieldFrame := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_take he
    simp [UpsV3.constraints, hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFieldFrame.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact fields_frame_q (hf _ (inst_mem hi) k hk) hp hC

end UpsGen
end ZkFormal.NearV3.Render
