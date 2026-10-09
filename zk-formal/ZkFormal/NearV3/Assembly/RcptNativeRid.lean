import ZkFormal.NearV3.Assembly.RcptNativePeo

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

def HeightPublicBytes (ctx : ApplyCtx) (pub : List Fp) : Prop :=
  ∀i,i<8→pub.getD (PH_HEIGHT+i) 0=Fp.ofNat (((u64 ctx.height).getD i 0).toNat)

theorem native_height_bytes (ctx : ApplyCtx) (pub : List Fp) (h : HeightPublicBytes ctx pub) :
    pubBytes pub PH_HEIGHT 8=(u64 ctx.height).map UInt8.toNat := by
  apply List.ext_getElem
  · simp [pubBytes,u64,leN]
  · intro i h1 h2
    have hi : i<8 := by simpa [pubBytes] using h1
    have hl : i<(u64 ctx.height).length := by simpa [u64,leN] using hi
    simp only [pubBytes,List.getElem_map,List.getElem_range]
    change (pub.getD (PH_HEIGHT+i) 0).toNat=(u64 ctx.height)[i].toNat
    rw [h i hi,native_byte_decode]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hl,Option.getD_some]

theorem native_refund_digest (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb : plannedRows lists=pre++plannedReceiptRows p++post)
    (hid : p.input.receipt.receiptId.length=32) (hh : HeightPublicBytes ctx pub) :
    let x := rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        fallback headerFallback) 0) 0 (inputShape pre.length p.input)
    x.hr=true→x.rfid=(sha256 ((x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).map UInt8.ofNat)).map UInt8.toNat := by
  dsimp only
  intro hr
  have hrid : (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        fallback headerFallback) 0) 0 (inputShape pre.length p.input)).rid=
      p.input.receipt.receiptId.map UInt8.toNat := by
    change colAt (RoutingQCandidate.patchTrace _ 0) 0 _ 32 b=_
    rw [patch_byte_slice]
    exact native_rid_slice own ctx lists log constants pub (nativeDigests ctx digests) fallback headerFallback p pre post hb hid
  rw [hrid,native_height_bytes ctx pub hh]
  rw [native_refundid_slice own ctx lists log constants pub (nativeDigests ctx digests)
    fallback headerFallback p pre post hb hr
    (gasRefundReceipt p.input.receipt ctx.height (nativeSurplus ctx p.input.receipt)).receiptId
    (by simp [gasRefundReceipt,receiptIdFrom,ArenaCore.sha256_length])
    (by simp [nativeDigests,outcomeDigests,refundDigests,sXRI,sXLH])]
  simp only [List.map_append,List.map_map,Function.comp_def,UInt8.ofNat_toNat,List.map_id_fun]
  simp [gasRefundReceipt,receiptIdFrom,List.map_id,List.map_replicate,u64,leN]

end ZkFormal.NearV3.Assembly.RcptSkeleton
