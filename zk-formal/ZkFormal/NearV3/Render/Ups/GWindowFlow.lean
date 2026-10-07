import ZkFormal.NearV3.Render.Ups.GWindowRoles
import ZkFormal.NearV3.Render.Ups.WindowStep

/-! Child-window succession and persistence of window metadata. -/
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

def cWindowFlow : List Expr := (UpsV3.cFields.drop 40).take 10

set_option hygiene false in
macro "window_flow_mem" : tactic => `(tactic| (
  change ex ∈ [
    mul3 (c fe) (c sCH) (sub (Dsl.k 1) (.add (n sCH) (n sMEM))),
    mul3 (c fe) (c sCH) (sub (c lastw) (n sMEM)),
    mul3 (Dsl.not (c sCH)) (n sCH) (Dsl.not (n fw)),
    mul3 (c sCH) (Dsl.not (c fe)) (sub (n fw) (c fw)),
    mul3 (c sCH) (c fe) (.mul (n sCH) (n fw))] ++
    [lastw,wfr,tgt,wy,wn].map (fun x => mul3 (c sCH) (Dsl.not (c fe)) (sub (n x) (c x))) at hex
  simp only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))

/-- Away from child rows, the window rules are inactive unless the next row enters CH. -/
theorem window_flow_off {C D P : Nat → Int} {fst lst trn : Int}
    (hc : C sCH = 0) (hd : D sCH = 0) :
    ∀ ex ∈ cWindowFlow, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  simp only [sCH] at hc hd
  window_flow_mem <;> apply cast0 <;> ups_ev [hc,hd] <;> simp

theorem window_flow_qmid {I : UpsInst} {Q : UpsPartI} {k p u u' : Nat}
    (ok : FieldsOk Q)
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 187 → C x = QC I Q k p
      (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1
      (fieldAt Q.shape p).2.2.1 (fieldAt Q.shape p).2.2.2 u x)
    (hD : ∀ x, x < 187 → D x = QC I Q k (p + 1)
      (fieldAt Q.shape (p + 1)).1 (fieldAt Q.shape (p + 1)).2.1
      (fieldAt Q.shape (p + 1)).2.2.1 (fieldAt Q.shape (p + 1)).2.2.2 u' x) :
    ∀ ex ∈ cWindowFlow, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  by_cases hs : (fieldAt Q.shape p).1 = 7
  · by_cases he : (fieldAt Q.shape p).2.1 + 1 = (fieldAt Q.shape p).2.2.1
    · have hn := ok.window_next hs he
      rw [hn] at hD
      split at hD
      · rename_i hl
        window_flow_mem <;> apply cast0 <;> ups_ev [hC,hD] <;> cellsimp <;>
          simp [ind,hs,he,lastwV,LastwB,hl,fwV,FwB]
      · rename_i hl
        window_flow_mem <;> apply cast0 <;> ups_ev [hC,hD] <;> cellsimp <;>
          simp [ind,hs,he,lastwV,LastwB,hl,fwV,FwB]
    · have hlen : (fieldAt Q.shape p).2.2.1 = 32 := by rw [(ok.window hs).2.2]
      have hb : (fieldAt Q.shape p).2.1 < 32 := by
        rw [(ok.window hs).2.2]; exact Nat.mod_lt _ (by decide)
      have hn := fieldAt_next_inside Q.shape p (by omega)
      rw [hn] at hD
      window_flow_mem <;> apply cast0 <;> ups_ev [hC,hD] <;> cellsimp <;>
        simp only [ind,hs,he,ite_true,ite_false,Int.one_mul,Int.mul_one,Int.zero_mul,Int.mul_zero] <;> omega
  · by_cases hn : (fieldAt Q.shape (p+1)).1 = 7
    · have hw := ok.window_enter hs hn
      window_flow_mem <;> apply cast0 <;> ups_ev [hC,hD] <;> cellsimp <;>
        simp [ind,hs,hn,fwV,FwB,hw]
    · apply window_flow_off ?_ ?_ ex hex
      · simp only [sCH]; rw [hC _ (by decide)]; cellsimp; simp [ind,hs]
      · simp only [sCH]; rw [hD _ (by decide)]; cellsimp; simp [ind,hn]

/-- The window transition rules across every row boundary, including part boundaries. -/
theorem cWindowFlow_ok {insts : List UpsInst} (ok : UpsOk insts)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cWindowFlow := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q hq hr C D P hC hD
    apply window_flow_off
    · simp only [sCH]; rw [hC _ (by decide)]; rfl
    · simp only [sCH]; rw [hD _ (by decide)]
      by_cases h3 : t < 3
      · rw [nextRow ok.shape hq hr (rk' := .w (t+1)) (by simp [nextRK,h3]),rowCell_w]; rfl
      · rw [nextRow ok.shape hq hr (rk' := .v 0) (by simp [nextRK,h3]),rowCell_v]; rfl
  · intro i hi p hp q hq hr C D P hC hD
    apply window_flow_off
    · simp only [sCH]; rw [hC _ (by decide)]; rfl
    · simp only [sCH]; rw [hD _ (by decide)]
      by_cases hp1 : p+1 < L (inst insts i)
      · rw [nextRow ok.shape hq hr (rk' := .v (p+1)) (by simp [nextRK,hp1]),rowCell_v]; rfl
      · rw [nextRow ok.shape hq hr (rk' := .q 0 0) (by simp [nextRK,hp1]),rowCell_q]
        rw [(hf _ (inst_mem hi) 0 (by have := (ok.inst _ (inst_mem hi)).nQ1; omega)).first]
        rfl
  · intro i hi k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p+1 < (part (inst insts i) k).q.length
    · apply window_flow_qmid (hf _ (inst_mem hi) k hk) hC
      intro x hx
      rw [hD x hx,nextRow ok.shape hq hr (rk' := .q k (p+1)) (by simp [nextRK,hp1]),rowCell_q]
    · apply window_flow_off
      · have hl : p+1 = (part (inst insts i) k).q.length := by omega
        have hs := (((ok.inst _ (inst_mem hi)).memEnd k hk p hp).1 hl).1
        simp only [sCH]; rw [hC _ (by decide)]; cellsimp; simp [ind,hs]
      · simp only [sCH]; rw [hD _ (by decide)]
        by_cases hk1 : k+1 < nQ (inst insts i)
        · rw [nextRow ok.shape hq hr (rk' := .q (k+1) 0) (by simp [nextRK,hp1,hk1]),rowCell_q]
          rw [(hf _ (inst_mem hi) (k+1) hk1).first]
          rfl
        · have hn : nextRK (inst insts i) (.q k p) = none := by simp [nextRK,hp1,hk1]
          rcases nextLast ok.shape hq hr hn 113 with h | ⟨_,h⟩
          · exact h
          · rw [h,rowCell_w]; rfl

end UpsGen
end ZkFormal.NearV3.Render
