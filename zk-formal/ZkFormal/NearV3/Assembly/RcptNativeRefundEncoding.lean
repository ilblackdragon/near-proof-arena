import ZkFormal.NearV3.Assembly.RcptNativeEncoding
import ZkFormal.NearV3.Assembly.RcptNativeRefundAmount
import ZkFormal.NearV3.Assembly.RcptNativePeo

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- The public refund-body bytes emitted by an honest receipt are exactly the
native gasRefundReceipt serialization, including its actual surplus amount. -/
theorem native_refund_encoding (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb : plannedRows lists=pre++plannedReceiptRows p++post)
    (hw : p.input.receipt.wf=true) (hflag : p.input.refund=nativeRefund ctx p.input.receipt)
    (hr : p.input.refund=true) :
    (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0
      (inputShape pre.length p.input)).encRefund=
        (gasRefundReceipt p.input.receipt ctx.height (nativeSurplus ctx p.input.receipt)).encode.map UInt8.toNat := by
  have hl : p.input.receipt.signerId.length≤64 ∧ p.input.receipt.signerPk.tag≤1 ∧
      p.input.receipt.signerPk.data.length=32+32*p.input.receipt.signerPk.tag := by
    simp only [Receipt.wf,AccountId.valid,PublicKey.wf,Bool.and_eq_true,Bool.or_eq_true,
      decide_eq_true_eq,beq_iff_eq] at hw
    grind only
  have ham : nativeRefundAmount ctx p.input.receipt=nativeSurplus ctx p.input.receipt := by
    apply nativeRefundAmount_ordinary
    intro hs
    have hn := nativeRefund_system ctx p.input.receipt hs
    rw [←hflag,hr] at hn
    cases hn
  unfold RcptV.encRefund
  rw [native_signer_slice own ctx lists log constants pub (nativeDigests ctx digests)
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback p pre post hb]
  rw [native_publickey_slice own ctx lists log constants pub (nativeDigests ctx digests)
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback p pre post hb hl.2.2]
  rw [native_refund_amount_slice own ctx k lists accountId accessId log constants pub (nativeDigests ctx digests)
    fallback headerFallback p pre post hb,ham]
  rw [native_refundid_slice own ctx lists log constants pub (nativeDigests ctx digests)
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback p pre post hb hr
    (gasRefundReceipt p.input.receipt ctx.height (nativeSurplus ctx p.input.receipt)).receiptId
    (by simp [gasRefundReceipt,receiptIdFrom,ArenaCore.sha256_length])
    (by simp [nativeDigests,outcomeDigests,refundDigests,sXRI,sXLH])]
  have hsys : (borshBytes AccountId.system).map UInt8.toNat=[6,0,0,0]++systemN := by decide
  simp only [Receipt.encode,gasRefundReceipt,List.map_append,hsys,native_borsh_bytes _ hl.1,
    native_publickey_bytes _ hl.2.1,rcptOf,inputShape]
  simp [tailN,u32,u128,leN,List.append_assoc]

end ZkFormal.NearV3.Assembly.RcptSkeleton
