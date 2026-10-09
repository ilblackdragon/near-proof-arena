import ZkFormal.NearV3.Assembly.RcptNativeByteCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

theorem native_byte_decode (x : UInt8) : (Fp.ofNat x.toNat).toNat=x.toNat := by
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt]
  have h := x.toNat_lt
  unfold Algebra.P
  omega

/-- Byte-valued physical slices decode without field reduction. -/
theorem native_slice (tr : Trace Fp) (start : Nat) (xs : Bytes)
    (hc : ∀i (hi : i<xs.length),tr.cell 0 (start+i) b=Fp.ofNat ((xs[i]'hi).toNat)) :
    colAt tr 0 start xs.length b=xs.map UInt8.toNat := by
  apply List.ext_getElem
  · simp [colAt]
  · intro i h1 h2
    have hi : i<xs.length := by simpa using h2
    simp only [colAt,List.getElem_map,List.getElem_range,cv,hc i hi,native_byte_decode]

/-- The native receipt ID is read from its concrete block in the complete trace. -/
theorem native_rid_slice (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (pre post : List PlannedRow) (hb : plannedRows lists=pre++plannedReceiptRows p++post)
    (hid : p.input.receipt.receiptId.length=32) :
    (rcptOf (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0
      (inputShape pre.length p.input)).rid=p.input.receipt.receiptId.map UInt8.toNat := by
  change colAt _ 0 (pre.length+(8+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length)) 32 b=_
  rw [←hid]
  apply native_slice
  intro i hi
  have hp := receipt_rid_position p i (by omega)
  have ha := receipt_block_lookup lists p pre post hb _ _ hp
  have hc := native_rid_cell own ctx lists log _ i constants pub digests fallback headerFallback p ha
  simpa only [Nat.add_assoc,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using hc

/-- The supplied partial-outcome digest is decoded at its exact physical field. -/
theorem native_peoh_slice (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan)
    (pre post : List PlannedRow) (hb : plannedRows lists=pre++plannedReceiptRows p++post)
    (digest : Bytes) (hlen : digest.length=32)
    (hd : digests p sXLH=digest.map (fun x=>Fp.ofNat x.toNat)) :
    (rcptOf (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0
      (inputShape pre.length p.input)).peoh=digest.map UInt8.toNat := by
  change colAt _ 0 (pre.length+(144+32*hN p.input.refund+
    Vt p.input.receipt.predecessorId.length p.input.receipt.receiverId.length
      p.input.receipt.signerId.length p.input.receipt.signerPk.tag)) 32 b=_
  rw [←hlen]
  apply native_slice
  intro i hi
  have hp := receipt_peoh_position p i (by omega)
  have ha := receipt_block_lookup lists p pre post hb _ _ hp
  have hc := native_peoh_cell own ctx lists log _ i constants pub digests fallback headerFallback p ha
  rw [hd] at hc
  simpa only [hlen,hN,Vt,Nat.add_assoc,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some] using hc

end ZkFormal.NearV3.Assembly.RcptSkeleton
