import ZkFormal.NearV3.Assembly.RcptNativePeoPositions

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

variable (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (pre post : List PlannedRow) (hb : plannedRows lists=pre++plannedReceiptRows p++post)

private abbrev nativeTrace := RoutingQCandidate.patchTrace
  (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0

include hb in
theorem native_receiver_slice :
    (rcptOf (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0
      (inputShape pre.length p.input)).v=p.input.receipt.receiverId.map UInt8.toNat := by
  change colAt _ 0 (pre.length+(8+p.input.receipt.predecessorId.length)) p.input.receipt.receiverId.length b=_
  rw [patch_byte_slice]
  apply native_slice
  intro i hi
  have ha := receipt_block_lookup lists p pre post hb _ _ (receipt_receiver_position p i hi)
  have hc := booleanReceiptTrace_planned_cell own ctx lists log _ constants pub digests fallback headerFallback _ ha b (by decide)
  change _=Fp.ofNat ((p.input.receipt.receiverId.getD i 0).toNat) at hc
  simpa only [Nat.add_assoc,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using hc

include hb in
theorem native_refundid_slice (hr : p.input.refund=true) (digest : Bytes) (hlen : digest.length=32)
    (hd : digests p sXRI=digest.map (fun x=>Fp.ofNat x.toNat)) :
    (rcptOf (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0
      (inputShape pre.length p.input)).rfid=digest.map UInt8.toNat := by
  simp only [rcptOf,inputShape,hr,ite_true]
  rw [patch_byte_slice]
  change colAt _ 0 (pre.length+(127+Vt p.input.receipt.predecessorId.length
      p.input.receipt.receiverId.length p.input.receipt.signerId.length p.input.receipt.signerPk.tag)) 32 b=_
  rw [←hlen]
  apply native_slice
  intro i hi
  have ha := receipt_block_lookup lists p pre post hb _ _ (receipt_refundid_position p hr i (by omega))
  have hc := booleanReceiptTrace_planned_cell own ctx lists log _ constants pub digests fallback headerFallback _ ha b (by decide)
  change _=(digests p sXRI).getD i 0 at hc
  rw [hd] at hc
  simpa only [Vt,Nat.add_assoc,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some] using hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
