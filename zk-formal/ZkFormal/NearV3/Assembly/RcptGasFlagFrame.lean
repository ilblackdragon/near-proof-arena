import ZkFormal.NearV3.Assembly.RcptGasFlagArithmetic
import ZkFormal.NearV3.Assembly.RcptGasDelayNativeComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasFlagInverse (ctx : ApplyCtx) (r : Receipt) : Fp :=
  if nativeRefund ctx r then (Fp.ofNat (gasDifferenceSum ctx r 16))⁻¹ else 0

def gasFlagAux (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if row.state=sGP ∧ col=sumD then Fp.ofNat (gasDifferenceSum ctx p.input.receipt (row.index+1)) else
  if row.state=sGP ∧ col=invA then gasFlagInverse ctx p.input.receipt else fallback p row col

theorem gasFlag_sum_cell (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasFlagAux ctx fallback)))
      p ⟨sGP,i,len⟩ sumD=Fp.ofNat (gasDifferenceSum ctx p.input.receipt (i+1)) := rfl

theorem gasFlag_inverse_cell (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasFlagAux ctx fallback)))
      p ⟨sGP,i,len⟩ invA=gasFlagInverse ctx p.input.receipt := rfl

theorem gasFlag_inverse_correct (ctx : ApplyCtx) (r : Receipt)
    (hg : r.gasPrice<256^16) (hc : ctx.gasPrice<256^16) :
    Fp.ofNat (gasDifferenceSum ctx r 16)*gasFlagInverse ctx r=bitCell (nativeRefund ctx r) := by
  by_cases hr : nativeRefund ctx r=true
  · have hn := gasDifferenceSum_refund_nonzero ctx r hg hc hr
    have hb := gasDifferenceSum_bound ctx r 16
    have hz : Fp.ofNat (gasDifferenceSum ctx r 16)≠0 := by
      intro hz
      have he := congrArg Fp.toNat hz
      rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)] at he
      exact hn he
    simp only [gasFlagInverse,hr,ite_true,bitCell]
    exact Fp.mul_inv_cancel hz
  · have hr' : nativeRefund ctx r=false := Bool.eq_false_iff.mpr hr
    simp only [gasFlagInverse,hr',Bool.false_eq_true,ite_false,bitCell]
    grind only

theorem gasFlag_noRefund_product (ctx : ApplyCtx) (r : Receipt) (i : Nat) :
    (1-bitCell (nativeRefund ctx r))*
      bitCell (decide (ctx.gasPrice≤r.gasPrice) && !(r.predecessorId==AccountId.system))*
      Fp.ofNat (gasDifference ctx r i)=0 := by
  by_cases hr : nativeRefund ctx r=true
  · simp only [hr,bitCell,ite_true];grind only
  · have hr' := Bool.eq_false_iff.mpr hr
    by_cases hs : r.predecessorId=AccountId.system
    · simp only [hs,beq_self_eq_true,Bool.not_true,Bool.and_false,bitCell,Bool.false_eq_true,ite_false]
      grind only
    · by_cases hg : ctx.gasPrice≤r.gasPrice
      · rw [gasDifference_no_refund ctx r hs hr' hg i]
        change _*(0:Fp)=0
        grind only
      · simp only [hg,decide_false,Bool.false_and,bitCell,Bool.false_eq_true,ite_false]
        grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
