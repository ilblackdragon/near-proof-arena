import ZkFormal.NearV3.Assembly.RcptNativePeoSlices
import ZkFormal.NearV3.Assembly.RcptNativeBurntCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

def refundDigests (ctx : ApplyCtx) (fallback : ReceiptPlan→Nat→List Fp)
    (p : ReceiptPlan) (state : Nat) : List Fp :=
  if state=sXRI then (gasRefundReceipt p.input.receipt ctx.height
    (nativeSurplus ctx p.input.receipt)).receiptId.map (fun x=>Fp.ofNat x.toNat)
  else fallback p state

def nativeDigests (ctx : ApplyCtx) (fallback : ReceiptPlan→Nat→List Fp) : ReceiptPlan→Nat→List Fp :=
  outcomeDigests ctx (refundDigests ctx fallback)

private theorem bytes_u32_small (n : Nat) (hn : n<256) : (u32 n).map UInt8.toNat=u32r n := by
  simp [u32,leN,u32r,Nat.mod_eq_of_lt hn,Nat.div_eq_of_lt hn]

/-- Semantic PEO compatibility includes system zero-token outcomes and the
native refund identifier; it does not assume a hash equation. -/
theorem peo_native_fields (ctx : ApplyCtx) (r : Receipt) (x : RcptE)
    (hvlen : r.receiverId.length≤64)
    (hh : x.hr=nativeRefund ctx r)
    (hv : x.v=r.receiverId.map UInt8.toNat)
    (hb : x.burnt=(u128 (nativeOutcome ctx r).tokensBurnt).map UInt8.toNat)
    (hr : x.hr=true→x.rfid=(gasRefundReceipt r ctx.height (nativeSurplus ctx r)).receiptId.map UInt8.toNat) :
    x.peo=(nativeOutcome ctx r).partialEncode.map UInt8.toNat := by
  have hg : (u64 Params.G).map UInt8.toNat=G_LEn := by decide
  have hbor : (borshBytes r.receiverId).map UInt8.toNat=RcptV.borshN (r.receiverId.map UInt8.toNat) := by
    simp only [borshBytes,List.map_append,bytes_u32_small r.receiverId.length (by omega),RcptV.borshN,List.length_map]
  unfold RcptV.peo
  rw [hv,hb]
  cases he : x.hr
  · have hn : nativeRefund ctx r=false := hh.symm.trans he
    simp only [he,Bool.false_eq_true,ite_false,nativeOutcome,hn,Outcome.partialEncode,
      List.length_nil,List.map_append,hg,hbor,concatAll,List.foldr_nil,List.append_nil,
      bytes_u32_small 0 (by decide)]
    simp [List.append_assoc,u32r,u32,leN]
  · have hn : nativeRefund ctx r=true := hh.symm.trans he
    rw [hr he]
    simp only [he,ite_true,nativeOutcome,hn,Outcome.partialEncode,List.length_singleton,
      List.map_append,hg,hbor,concatAll,List.foldr_cons,List.foldr_nil,List.append_nil,
      bytes_u32_small 1 (by decide)]
    simp [List.append_assoc,u32r,u32,leN]

/-- All fields of the actual honest trace's PEO match native serialization,
using the complete arithmetic auxiliary assignment and native refund digest. -/
theorem native_peo_slice (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb : plannedRows lists=pre++plannedReceiptRows p++post)
    (hw : p.input.receipt.wf=true) (hflag : p.input.refund=nativeRefund ctx p.input.receipt) :
    (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0
      (inputShape pre.length p.input)).peo=
        (nativeOutcome ctx p.input.receipt).partialEncode.map UInt8.toNat := by
  apply peo_native_fields ctx p.input.receipt
  · simp only [Receipt.wf,AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hw
    grind only
  · exact hflag
  · exact native_receiver_slice own ctx lists log constants pub (nativeDigests ctx digests)
      (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback p pre post hb
  · exact native_burnt_slice own ctx k lists accountId accessId log constants pub (nativeDigests ctx digests)
      fallback headerFallback p pre post hb
  · intro hr
    apply native_refundid_slice own ctx lists log constants pub (nativeDigests ctx digests)
      (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback p pre post hb hr
    · simp [gasRefundReceipt,receiptIdFrom,ArenaCore.sha256_length]
    · simp [nativeDigests,outcomeDigests,refundDigests,sXRI,sXLH]

/-- The actual digest field hashes the same PEO bytes that this view emits. -/
theorem native_peo_digest (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb : plannedRows lists=pre++plannedReceiptRows p++post)
    (hw : p.input.receipt.wf=true) (hflag : p.input.refund=nativeRefund ctx p.input.receipt) :
    let x := rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0
      (inputShape pre.length p.input)
    x.peoh=(sha256 (x.peo.map UInt8.ofNat)).map UInt8.toNat := by
  dsimp only
  rw [native_peo_slice own ctx k lists accountId accessId log constants pub digests fallback headerFallback p pre post hb hw hflag]
  simp only [List.map_map,Function.comp_def,UInt8.ofNat_toNat,List.map_id_fun]
  change colAt (RoutingQCandidate.patchTrace _ 0) 0 _ 32 b=_
  rw [patch_byte_slice]
  exact native_peoh_slice own ctx lists log constants pub (nativeDigests ctx digests)
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback p pre post hb
    _ (ArenaCore.sha256_length _) (by simp [nativeDigests,outcomeDigests])

end ZkFormal.NearV3.Assembly.RcptSkeleton
