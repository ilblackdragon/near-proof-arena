import ZkFormal.NearV3.Assembly.RcptNativePeoSlices

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- Decode a complete native byte field at its actual prefix offset. This works
for all non-register input fields and preserves the routing-q trace patch. -/
theorem native_field_slice (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (pre post : List PlannedRow) (hb : plannedRows lists=pre++plannedReceiptRows p++post)
    (index state off : Nat) (bytes : Bytes)
    (hk : (fields p.input.refund)[index]?=some state)
    (hp : (((fields p.input.refund).take index).flatMap (fun s=>segment s (fieldLen p.input s))).length=off)
    (hl : bytes.length=fieldLen p.input state)
    (hg : state∉regStates)
    (hv : ∀i,nativeFieldByte p ⟨state,i,fieldLen p.input state⟩=Fp.ofNat ((bytes.getD i 0).toNat)) :
    colAt (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0)
      0 (pre.length+off) bytes.length b=bytes.map UInt8.toNat := by
  rw [patch_byte_slice]
  apply native_slice
  intro i hi
  have hf := field_lookup p.input (fields p.input.refund) index state i hk (by omega)
  rw [hp] at hf
  have hr : (plannedReceiptRows p)[off+i]?=some (.receipt p ⟨state,i,fieldLen p.input state⟩) := by
    simp only [plannedReceiptRows,receiptRows,List.getElem?_map]
    rw [hf];rfl
  have ha := receipt_block_lookup lists p pre post hb _ _ hr
  have hc := booleanReceiptTrace_planned_cell own ctx lists log _ constants pub digests fallback headerFallback _ ha b (by decide)
  change _=(if state∈regStates then (receiptStream pub digests p state).getD i 0 else nativeFieldByte p ⟨state,i,fieldLen p.input state⟩) at hc
  rw [if_neg hg,hv i] at hc
  simpa only [Nat.add_assoc,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
