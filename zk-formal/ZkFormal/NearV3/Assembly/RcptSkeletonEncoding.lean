import ZkFormal.NearV3.Assembly.RcptSkeletonPlan

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

/-- The source-list offset increment is the actual native serialization length,
including both accepted public-key variants and system receipts. -/
theorem rcLength_native (x : Input) (hw : x.receipt.wf=true) :
    x.receipt.encode.length=rcLength x := by
  have hs : x.receipt.receiptId.length=32 ∧
      x.receipt.signerPk.data.length=32+32*x.receipt.signerPk.tag := by
    simp only [Receipt.wf,PublicKey.wf,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at hw
    grind only
  simp only [Receipt.encode,PublicKey.encode,borshBytes,List.length_append,u8,u32,u128,leN,
    List.length_cons,List.length_nil,hs.1,hs.2,rcLength]
  omega

/-- Refund-body offset increments are exact for the native gasRefundReceipt;
height and refund amount do not change this length, and both public-key tags work. -/
theorem refundLength_native (x : Input) (hw : x.receipt.wf=true) (height amount : Nat) :
    refundLength x=(if x.refund then (gasRefundReceipt x.receipt height amount).encode.length else 0) := by
  have hpk : x.receipt.signerPk.data.length=32+32*x.receipt.signerPk.tag := by
    simp only [Receipt.wf,PublicKey.wf,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at hw
    grind only
  cases hr : x.refund
  · simp only [refundLength,hr,Bool.false_eq_true,ite_false]
  · simp only [refundLength,hr,ite_true,Receipt.encode,gasRefundReceipt,PublicKey.encode,borshBytes,
      List.length_append,u8,u32,u128,leN,List.length_cons,List.length_nil,receiptIdFrom,
      ArenaCore.sha256_length,AccountId.system,hpk]
    omega

/-- A fully annotated receipt plan advances the committed RC stream by the exact
bytes that native receipt serialization consumes. -/
theorem planReceipts_native_step (x : Input) (xs : List Input) (j nj r cj o o2 : Nat)
    (ll : Bool) (hw : x.receipt.wf=true) :
    (planReceipts j nj r cj o o2 ll (x::xs)).tail=
      planReceipts j nj (r+1) (cj+1) (o+x.receipt.encode.length)
        (o2+refundLength x) ll xs := by
  rw [rcLength_native x hw]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
