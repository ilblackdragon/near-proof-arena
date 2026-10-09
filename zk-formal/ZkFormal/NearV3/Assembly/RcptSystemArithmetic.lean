import ZkFormal.NearV3.Assembly.RcptSystemCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem system_no_refund (ctx : ApplyCtx) (r : Receipt) :
    bitCell (r.predecessorId==AccountId.system)*bitCell (nativeRefund ctx r)=0 := by
  by_cases hs : r.predecessorId=AccountId.system
  · rw [nativeRefund_system ctx r hs]
    simp only [bitCell,Bool.false_eq_true,ite_false]
    grind only
  · simp only [beq_eq_false_iff_ne.mpr hs,bitCell,Bool.false_eq_true,ite_false]
    grind only

theorem system_length_inverse (r : Receipt) (hw : r.wf=true) :
    (bitCell (r.predecessorId==AccountId.system)-bitCell (systemEqual r)-bitCell (systemMismatch r))*
      ((Fp.ofNat r.signerId.length-Fp.ofNat r.receiverId.length)*
        (Fp.ofNat r.signerId.length-Fp.ofNat r.receiverId.length)⁻¹-1)=0 := by
  by_cases hl : r.signerId.length=r.receiverId.length
  · have hd : systemEqualLength r=true := by simp only [systemEqualLength,hl,beq_self_eq_true]
    have hh := system_identity_arithmetic r
    have hbit : bitCell (systemEqualLength r)=1 := by simp only [hd,bitCell,ite_true]
    rw [hbit] at hh
    grind only
  · have hls : r.signerId.length≤64 :=
      (characterBytes_bounds ⟨r,false⟩ hw sS (by decide)).2
    have hlv : r.receiverId.length≤64 :=
      (characterBytes_bounds ⟨r,false⟩ hw sV (by decide)).2
    have hh := native_diff_nonzero r.signerId.length r.receiverId.length
      (Nat.lt_of_le_of_lt hls (by decide)) (Nat.lt_of_le_of_lt hlv (by decide)) hl
    rw [Fp.mul_inv_cancel hh]
    grind only

theorem system_byte_inverse (r : Receipt) (i : Nat)
    (h : systemMismatch r=true) (hi : i=firstMismatch r.signerId r.receiverId) :
    (Fp.ofNat ((r.signerId.getD i 0).toNat)-Fp.ofNat ((r.receiverId.getD i 0).toNat))*
      (Fp.ofNat ((r.signerId.getD i 0).toNat)-Fp.ofNat ((r.receiverId.getD i 0).toNat))⁻¹=1 := by
  obtain ⟨_,_,_,hne⟩ := systemMismatch_witness r h
  rw [←hi] at hne
  have hne' : (r.signerId.getD i 0).toNat≠(r.receiverId.getD i 0).toNat := by
    intro hh
    exact hne (UInt8.toNat_inj.mp hh)
  have ha := (r.signerId.getD i 0).toNat_lt
  have hb := (r.receiverId.getD i 0).toNat_lt
  apply Fp.mul_inv_cancel
  apply native_diff_nonzero _ _ _ _ hne'
  · exact Nat.lt_trans ha (by decide)
  · exact Nat.lt_trans hb (by decide)

end ZkFormal.NearV3.Assembly.RcptSkeleton
