import ZkFormal.NearV3.Assembly.RcptNativeSlices
import ZkFormal.NearV3.Assembly.RcptNativeOutcomes

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- Bind digest streams directly to the native per-receipt outcome. -/
def outcomeDigests (ctx : ApplyCtx) (fallback : ReceiptPlan→Nat→List Fp)
    (p : ReceiptPlan) (st : Nat) : List Fp :=
  if st=sXLH then (sha256 (nativeOutcome ctx p.input.receipt).partialEncode).map
    (fun x=>Fp.ofNat x.toNat) else fallback p st

theorem patch_byte_slice (tr : Trace Fp) (start len : Nat) :
    colAt (RoutingQCandidate.patchTrace tr 0) 0 start len b=colAt tr 0 start len b := by
  unfold colAt cv
  apply List.map_congr_left
  intro i hi
  rw [RoutingQCandidate.patch_other tr 0 (start+i) b (by decide)]

/-- Q-bit repair preserves the two byte fields used by the outcome leaf. -/
theorem patch_leaf (tr : Trace Fp) (shape : RS) :
    (rcptOf (RoutingQCandidate.patchTrace tr 0) 0 shape).leaf=(rcptOf tr 0 shape).leaf := by
  simp only [RcptV.leaf,rcptOf,patch_byte_slice]

/-- The concrete physical receipt block carries the native outcome's leaf
preimage. Native execution order is handled separately by applyNewChunk_outcomes. -/
theorem native_leaf (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (pre post : List PlannedRow) (hb : plannedRows lists=pre++plannedReceiptRows p++post)
    (hid : p.input.receipt.receiptId.length=32) :
    (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (outcomeDigests ctx digests)
        fallback headerFallback) 0) 0 (inputShape pre.length p.input)).leaf=
      (u32 2++(nativeOutcome ctx p.input.receipt).id++
        sha256 (nativeOutcome ctx p.input.receipt).partialEncode).map UInt8.toNat := by
  rw [patch_leaf]
  unfold RcptV.leaf
  rw [native_rid_slice own ctx lists log constants pub (outcomeDigests ctx digests)
    fallback headerFallback p pre post hb hid]
  rw [native_peoh_slice own ctx lists log constants pub (outcomeDigests ctx digests)
    fallback headerFallback p pre post hb
    (sha256 (nativeOutcome ctx p.input.receipt).partialEncode) (ArenaCore.sha256_length _)
    (by simp only [outcomeDigests,ite_true])]
  simp only [List.map_append,nativeOutcome]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
