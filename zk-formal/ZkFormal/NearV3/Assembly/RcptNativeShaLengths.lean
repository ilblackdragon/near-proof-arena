import ZkFormal.NearV3.Assembly.RcptNativeOutcomes
import ZkFormal.NearV3.Rcpt.Candidates.ReceiptShaJobs

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near Rcpt.Candidates

/-- Byte cost follows native receipt well-formedness, without account/memory AIR
or extracted receipt-Wf assumptions. -/
theorem native_receipt_encoded_bound (r : Receipt) (hw : r.wf=true) : r.encode.length≤347 := by
  have hl : r.predecessorId.length≤64 ∧ r.receiverId.length≤64 ∧
      r.signerId.length≤64 ∧ r.signerPk.tag≤1 ∧ r.receiptId.length=32 ∧
      r.signerPk.data.length=32+32*r.signerPk.tag := by
    simp only [Receipt.wf,AccountId.valid,PublicKey.wf,Bool.and_eq_true,Bool.or_eq_true,
      decide_eq_true_eq,beq_iff_eq] at hw
    grind only
  simp only [Receipt.encode,PublicKey.encode,borshBytes,u8,u32,u128,leN,List.length_append,
    List.length_map,List.length_range,List.length_cons,List.length_nil]
  omega

theorem native_peo_length_bound (ctx : ApplyCtx) (r : Receipt) (hw : r.wf=true) :
    (nativeOutcome ctx r).partialEncode.length≤133 := by
  have hv : r.receiverId.length≤64 := by
    simp only [Receipt.wf,AccountId.valid,PublicKey.wf,Bool.and_eq_true,Bool.or_eq_true,
      decide_eq_true_eq,beq_iff_eq] at hw
    grind only
  unfold Outcome.partialEncode nativeOutcome
  cases h : nativeRefund ctx r <;>
    simp [h,concatAll,borshBytes,u32,u64,u128,leN,gasRefundReceipt,receiptIdFrom,ArenaCore.sha256_length] <;> omega

/-- Only physical preimage lengths are needed for the receipt SHA workload. -/
theorem receipt_sha_rows_of_lengths (pub : List Algebra.Fp) (x : RcptE)
    (hp : x.peo.length≤133) (hl : x.leaf.length=68) (hr : x.rid.length=32) :
    hashRows ((receiptShaPayloads pub x).map List.length)≤105 := by
  have hpm := Render.rowsOf_mono hp
  have hp133 : Render.rowsOf 133=52 := by decide
  have hl68 : Render.rowsOf 68=35 := by decide
  have hr48 : Render.rowsOf 48=18 := by decide
  have hrl : (x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).length=48 := by
    simp [hr,pubBytes]
  unfold receiptShaPayloads hashRows
  cases hx : x.hr <;>
    simp only [hx,Bool.false_eq_true,ite_false,ite_true,List.append_nil,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,List.cons_append,List.nil_append,hl,hrl,hl68,hr48] <;> omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
