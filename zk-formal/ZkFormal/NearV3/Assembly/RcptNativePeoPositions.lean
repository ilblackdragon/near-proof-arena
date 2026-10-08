import ZkFormal.NearV3.Assembly.RcptNativeLeaves

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near RcptV3

theorem receipt_receiver_position (p : ReceiptPlan) (i : Nat) (hi : i<p.input.receipt.receiverId.length) :
    (plannedReceiptRows p)[8+p.input.receipt.predecessorId.length+i]?=
      some (.receipt p ⟨sV,i,p.input.receipt.receiverId.length⟩) := by
  have hh := field_lookup p.input (fields p.input.refund) 3 sV i
    (by cases p.input.refund <;> rfl) (by simpa [fieldLen,sCL,sPL,sP,sVL,sV] using hi)
  have he : (((fields p.input.refund).take 3).flatMap (fun s=>segment s (fieldLen p.input s))).length=
      8+p.input.receipt.predecessorId.length := by
    cases p.input.refund <;> simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV] <;> omega
  rw [he] at hh
  simp only [plannedReceiptRows,receiptRows,List.getElem?_map]
  rw [hh]
  rfl

theorem receipt_refundid_position (p : ReceiptPlan) (hr : p.input.refund=true) (i : Nat) (hi : i<32) :
    (plannedReceiptRows p)[127+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length+
      p.input.receipt.signerId.length+32*p.input.receipt.signerPk.tag+i]?=
      some (.receipt p ⟨sXRI,i,32⟩) := by
  have hh := field_lookup p.input (fields p.input.refund) 14 sXRI i
    (by rw [hr];rfl)
    (by simpa [fieldLen,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,sXRI] using hi)
  have he : (((fields p.input.refund).take 14).flatMap (fun s=>segment s (fieldLen p.input s))).length=
      127+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length+
        p.input.receipt.signerId.length+32*p.input.receipt.signerPk.tag := by
    rw [hr]
    simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP,sTL,sDEP,sXP0,sXRI]
    omega
  rw [he] at hh
  simp only [plannedReceiptRows,receiptRows,List.getElem?_map]
  rw [hh]
  rfl

theorem receipt_gas_position (p : ReceiptPlan) (i : Nat) (hi : i<16) :
    (plannedReceiptRows p)[78+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length+
      p.input.receipt.signerId.length+32*p.input.receipt.signerPk.tag+i]?=
      some (.receipt p ⟨sGP,i,16⟩) := by
  have hh := field_lookup p.input (fields p.input.refund) 10 sGP i
    (by cases p.input.refund <;> rfl)
    (by simpa [fieldLen,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP] using hi)
  have he : (((fields p.input.refund).take 10).flatMap (fun s=>segment s (fieldLen p.input s))).length=
      78+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length+
        p.input.receipt.signerId.length+32*p.input.receipt.signerPk.tag := by
    cases p.input.refund <;>
      simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,sGP] <;> omega
  rw [he] at hh
  simp only [plannedReceiptRows,receiptRows,List.getElem?_map]
  rw [hh]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
