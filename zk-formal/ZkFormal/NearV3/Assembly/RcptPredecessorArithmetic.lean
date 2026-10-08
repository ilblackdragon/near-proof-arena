import ZkFormal.NearV3.Assembly.RcptPredecessorBytes

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

theorem predecessor_score_start (r : Receipt) :
    Fp.ofNat (accP (characterData r) 0)=
      (Fp.ofNat ((characterData r).pred.getD 0 0)-Fp.ofNat (sysB 0))^
        (2:Nat) := by
  rw [accP_zero,ofNat_sqd]
  grind only

theorem predecessor_score_step (r : Receipt) (i : Nat) :
    Fp.ofNat (accP (characterData r) (i+1))=Fp.ofNat (accP (characterData r) i)+
      (Fp.ofNat ((characterData r).pred.getD (i+1) 0)-Fp.ofNat (sysB (i+1)))^
        (2:Nat) := by
  rw [accP_succ,ofNat_add_e,ofNat_sqd]
  grind only

theorem predecessor_system_length (r : Receipt) :
    bitCell (r.predecessorId==AccountId.system)*(Fp.ofNat r.predecessorId.length-6)=0 := by
  by_cases h : r.predecessorId=AccountId.system
  · simp only [h,beq_self_eq_true,bitCell,ite_true]
    change (1:Fp)*(6-6)=0
    grind only
  · have he : (r.predecessorId==AccountId.system)=false := by simpa only [beq_eq_false_iff_ne] using h
    simp only [he,bitCell,Bool.false_eq_true,ite_false]
    grind only

/-- All six scalar identities used by predecessor/system constraints, on native
bytes. The physical next-row transport is proved separately. -/
theorem predecessor_native_equations (r : Receipt) (hv : AccountId.valid r.predecessorId=true)
    (i : Nat) (hi : i+1=r.predecessorId.length) :
    let d := characterData r
    Fp.ofNat (accP d 0)=(Fp.ofNat (d.pred.getD 0 0)-Fp.ofNat (sysB 0))^2 ∧
    (∀j,Fp.ofNat (accP d (j+1))=Fp.ofNat (accP d j)+
      (Fp.ofNat (d.pred.getD (j+1) 0)-Fp.ofNat (sysB (j+1)))^2) ∧
    Fp.ofNat (pP d)=Fp.ofNat (accP d i)+(Fp.ofNat r.predecessorId.length-6)^2 ∧
    Fp.ofNat (pP d)*(Fp.ofNat (pP d))⁻¹=1-bitCell (r.predecessorId==AccountId.system) ∧
    bitCell (r.predecessorId==AccountId.system)*Fp.ofNat (pP d)=0 ∧
    bitCell (r.predecessorId==AccountId.system)*(Fp.ofNat r.predecessorId.length-6)=0 := by
  exact ⟨predecessor_score_start r,predecessor_score_step r,
    by have h := predecessor_score_end r i hi; grind only, (character_pred_inverse r hv).1,
    (character_pred_inverse r hv).2,predecessor_system_length r⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
