import ZkFormal.NearV3.Render.Ups.GFieldPrefix
import ZkFormal.NearV3.Render.Ups.WindowRoles

/-! The eight window-role constraints determined by generator selectors. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Render.EvI ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

theorem gate_sub_eq {g a b : Int} (h : a = b) : g * (a + -b) = 0 := by
  rw [h,Int.add_right_neg,Int.mul_zero]

def cWindowRoles : List Expr := (UpsV3.cFields.drop 53).take 8

set_option hygiene false in
macro "window_roles_mem" : tactic => `(tactic| (
  change ex ∈ [
    .mul (c sCH) (sub (c tgt) (.add (.mul (c fw) (Dsl.not s15E)) (.mul (c lastw) s15E))),
    mul3 (.add (c kRDB) (c kRBI)) (c sCH) (sub (c wfr) (c tgt)),
    mul3 (sumc [kRDE,kWEX,kPT]) (c sCH) (Dsl.not (c wfr)),
    mul3 (sumc [kRBR,kRBV,kMVE]) (c sCH) (c wfr),
    mul3 (c kSPB) (c sCH) (sub (c wy) (.add (.mul (c fw) (c spY1)) (.mul (Dsl.not (c fw)) (c spY2)))),
    mul3 (c kSPB) (c sCH) (sub (c wfr) (sub (Dsl.k 1) (.mul (Dsl.not (c wy)) (c xcp)))),
    .mul (c sCH) (sub (c wn) (.add (.mul (c kRBI) (c tgt)) (.mul (c kSPB) (c wy)))),
    sub (c rdc) (.mul (mul3 (c sCH) (c fs) (c tgt)) (c UpsV3.up))] at hex
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))

theorem window_roles_q {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat}
    {C D P : Nat → Int} {fst lst trn : Int}
    (hC : ∀ x, x < 200 → C x = QC I Q k p st ix fl wi u x) :
    ∀ ex ∈ cWindowRoles, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  by_cases hs : st = 7
  · subst st
    window_roles_mem <;> apply cast0 <;> ups_ev [hC] <;> cellsimp <;>
      simp only [ind_True,Int.one_mul,Int.mul_one,Nat.ToInt.natCast_ofNat]
    · have ht := target_formula I Q wi
      rw [s15_formula] at ht
      simp only [Int.sub_eq_add_neg,Nat.ToInt.natCast_ofNat] at ht
      exact Int.sub_eq_zero.mpr ht
    · by_cases hk : Q.kind = 0 ∨ Q.kind = 5
      · rw [wfr_target I Q wi hk]; simp only [Int.add_right_neg,Int.mul_zero]
      · simp only [not_or] at hk
        simp [ind,hk.1,hk.2]
    · by_cases hk : Q.kind = 1 ∨ Q.kind = 9 ∨ Q.kind = 11
      · rw [wfr_fresh I Q wi hk]; simp
      · simp only [not_or] at hk
        simp [ind,hk.1,hk.2.1,hk.2.2]
    · by_cases hk : Q.kind = 3 ∨ Q.kind = 4 ∨ Q.kind = 7
      · rw [wfr_copy I Q wi hk]; simp
      · simp only [not_or] at hk
        simp [ind,hk.1,hk.2.1,hk.2.2]
    · by_cases hk : Q.kind = 10
      · exact gate_sub_eq (wy_formula I Q wi hk)
      · simp [ind,hk]
    · by_cases hk : Q.kind = 10
      · exact gate_sub_eq (wfr_split I Q wi hk)
      · simp [ind,hk]
    · have ht := wn_formula I Q wi
      omega
    · have ht := rdc_formula I Q ix wi
      omega
  · window_roles_mem <;> apply cast0 <;> ups_ev [hC] <;> cellsimp <;>
      simp [ind,hs,rdcV,RdcB]

/-- Window-role formulas hold for every honest generated row, without new instance inputs. -/
theorem cWindowRoles_ok {insts : List UpsInst} (ok : UpsOk insts)
    {H : Nat} (hH : R insts + 1 ≤ H) : GroupOk insts H cWindowRoles := by
  apply groupOk_by ok hH (fun e he => by
    have hm : e ∈ UpsV3.cFields := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [UpsV3.constraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]
      exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cWindowRoles.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi p hp q _ _
    exact actV_vz (by decide)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact window_roles_q hC

end UpsGen
end ZkFormal.NearV3.Render
