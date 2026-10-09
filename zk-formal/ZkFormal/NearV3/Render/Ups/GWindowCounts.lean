import ZkFormal.NearV3.Render.Ups.GWindowFlow
import ZkFormal.NearV3.Render.Ups.WindowInput

/-! Extension and split-branch child-window counts. -/
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cWindowCounts : List Expr := (UpsV3.cFields.drop 50).take 3

set_option hygiene false in
macro "window_counts_mem" : tactic => `(tactic| (
  change ex ∈ [mul3 (c qte) (c sCH) (Dsl.not (c lastw)),
    .mul (mul3 (c kSPB) (c sCH) (c fw)) (sub (c lastw) (Dsl.not twoE)),
    mul3 (c kSPB) (c sCH) (.mul (Dsl.not (c fw)) (Dsl.not (c lastw)))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl))

theorem window_counts_q {I : UpsInst} {Q : UpsPartI} {k p u : Nat}
    (ok : FieldsOk Q) (wok : WindowOk I Q)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 200 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x) :
    ∀ ex ∈ cWindowCounts, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  by_cases hs : (fieldAt Q.shape p).1 = 7
  · have hw := ok.window_index hs
    window_counts_mem <;> apply cast0 <;> ups_ev [hC] <;> cellsimp <;>
      simp only [hs,ind_True,Int.one_mul,Int.mul_one]
    · by_cases ht : Q.ty = 1
      · have hn := ok.extension ht
        have he : (fieldAt Q.shape p).2.2.2 + 1 = nWin Q.shape := by omega
        simp [ind,lastwV,LastwB,ht,he]
      · simp [ind,ht]
    · by_cases hk : Q.kind = 10
      · have hn := wok.splitCount hk
        by_cases hf : (fieldAt Q.shape p).2.2.2 = 0
        · by_cases h6 : I.ci = 6 <;> by_cases h9 : I.ci = 9 <;> by_cases h10 : I.ci = 10 <;>
            simp [h6,h9,h10] at hn <;>
            simp [ind,lastwV,LastwB,fwV,FwB,hk,hf,hn,h6,h9,h10] <;> omega
        · simp [ind,fwV,FwB,hk,hf]
      · simp [ind,hk]
    · by_cases hk : Q.kind = 10
      · have hn := wok.splitCount hk
        have hn2 : nWin Q.shape ≤ 2 := by split at hn <;> omega
        by_cases hf : (fieldAt Q.shape p).2.2.2 = 0
        · simp [ind,fwV,FwB,hf]
        · have he : (fieldAt Q.shape p).2.2.2 + 1 = nWin Q.shape := by omega
          simp [ind,lastwV,LastwB,fwV,FwB,hk,hf,he]
      · simp [ind,hk]
  · window_counts_mem <;> apply cast0 <;> ups_ev [hC] <;> cellsimp <;> simp [ind,hs]

/-- Count constraints for the complete padded update trace. -/
theorem cWindowCounts_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hw : ∀ I ∈ insts, ∀ k, k < nQ I → WindowOk I (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cWindowCounts := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cWindowCounts.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact window_counts_q (hf _ (inst_mem hi) k hk) (hw _ (inst_mem hi) k hk) hC

end UpsGen
end ZkFormal.NearV3.Render
