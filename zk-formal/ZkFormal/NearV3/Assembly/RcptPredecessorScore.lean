import ZkFormal.NearV3.Assembly.RcptSeparatorComposition
import ZkFormal.Near.Render.Proof.RcptChars4

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

/-- Character-only projection into the reusable legacy arithmetic constructor.
No legacy Good predicate or old non-system domain restriction is imported. -/
def characterData (r : Receipt) : RD :=
  { (default : RD) with pred:=toNats r.predecessorId,recv:=toNats r.receiverId }

/-- Generalized from legacy RcptChars4.predOk, with actual bytes/validity and
an explicit non-system branch replacing legacy Good. Source SHA256: 1a7e148ba5cea2d2aed2b2cafb8bca5a31c1948aba9eefb2f2b284084076d28c. -/
theorem character_pred_nonzero (r : Receipt) (hv : AccountId.valid r.predecessorId=true)
    (hne : r.predecessorId≠AccountId.system) : PredOk (characterData r) := by
  have hS : StrOk (characterData r).pred := strOk_of r.predecessorId hv
  have hL := hS.len
  unfold PredOk pP
  rw [ofNat_mod]
  have hB : accP (characterData r) ((characterData r).pred.length - 1) ≤ 64 * 65025 := by
    have h3 := runSum_le (fun j => sqd ((characterData r).pred.getD j 0) (sysB j)) 65025 (fun j => by
      have h1 : (characterData r).pred.getD j 0 < 256 := by
        by_cases hj : j < (characterData r).pred.length
        · exact hS.byte j hj
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show (characterData r).pred.length ≤ j by omega)]
      have h2 : sysB j < 256 := by
        simp only [sysB_eq, List.getD_eq_getElem?_getD]
        rcases (show j < 6 ∨ 6 ≤ j by omega) with h | h
        · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
        · simp [List.getElem?_eq_none (show [115, 121, 115, 116, 101, 109].length ≤ j by simp; omega)]
      exact sqd_le h1 h2) ((characterData r).pred.length - 1)
    exact Nat.le_trans h3 (Nat.mul_le_mul_right _ (by omega))
  have hB2 : sqd (characterData r).pred.length 6 ≤ 90000 := sqd_small (by omega) (by omega)
  apply ofNat_ne_zero _ (by have := P_big; omega)
  intro h0
  have h6 : (characterData r).pred.length = 6 := sqd_eq_zero (by omega)
  have hz := runSum_eq_zero _ _ (show accP (characterData r) ((characterData r).pred.length - 1) = 0 by omega)
  apply hne
  apply toNats_inj
  rw [← show (characterData r).pred = toNats r.predecessorId by rfl]
  apply List.ext_getElem (by rw [h6]; rfl)
  intro j h1 h2
  have := sqd_eq_zero (hz j (by omega))
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some, sysB_eq] at this
  rw [this]
  rw [h6] at h1
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 by omega) with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem character_pred_system (r : Receipt) (h : r.predecessorId=AccountId.system) :
    pP (characterData r)=0 := by
  simp [characterData,h,AccountId.system,toNats,pP,accP,runSum,sqd,sysB,List.range_succ]

theorem character_pred_inverse (r : Receipt) (hv : AccountId.valid r.predecessorId=true) :
    Fp.ofNat (pP (characterData r))*(Fp.ofNat (pP (characterData r)))⁻¹=
      1-bitCell (r.predecessorId==AccountId.system) ∧
    bitCell (r.predecessorId==AccountId.system)*Fp.ofNat (pP (characterData r))=0 := by
  by_cases hs : r.predecessorId=AccountId.system
  · rw [character_pred_system r hs]
    simp only [hs,beq_self_eq_true,bitCell,ite_true]
    change (0:Fp)*0⁻¹=1-1 ∧ (1:Fp)*0=0
    constructor <;> grind only
  · have hn := character_pred_nonzero r hv hs
    rw [Fp.mul_inv_cancel hn]
    have he : (r.predecessorId==AccountId.system)=false := by simpa only [beq_eq_false_iff_ne] using hs
    simp only [he,bitCell,Bool.false_eq_true,ite_false]
    constructor <;> grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
