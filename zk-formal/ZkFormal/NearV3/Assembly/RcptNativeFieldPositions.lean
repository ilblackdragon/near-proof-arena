import ZkFormal.NearV3.Assembly.RcptCandidateRepairedTable
import ZkFormal.NearV3.Assembly.RcptCandidateOf

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near RcptV3

/-- Exact indexed location inside the concatenated native field segments. -/
theorem field_lookup (x : Input) (ss : List Nat) (k st i : Nat)
    (hk : ss[k]?=some st) (hi : i<fieldLen x st) :
    (ss.flatMap (fun s=>segment s (fieldLen x s)))[((ss.take k).flatMap (fun s=>segment s (fieldLen x s))).length+i]?=
      some ⟨st,i,fieldLen x st⟩ := by
  induction ss generalizing k with
  | nil => simp at hk
  | cons s ss ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hk
      subst st
      simp only [List.take_zero,List.flatMap_nil,List.length_nil,Nat.zero_add,List.flatMap_cons]
      rw [List.getElem?_append_left (by rw [segment_length];exact hi)]
      simp only [segment,List.getElem?_map,List.getElem?_range hi,Option.map_some]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      simp only [List.take_succ_cons,List.flatMap_cons,List.length_append]
      rw [List.getElem?_append_right (by omega)]
      simpa only [Nat.add_assoc,Nat.add_sub_cancel_left] using ih k hk

def inputShape (start : Nat) (x : Input) : RcptV3Proof.RS :=
  ⟨start,x.refund,x.receipt.predecessorId.length,x.receipt.receiverId.length,
    x.receipt.signerId.length,x.receipt.signerPk.tag⟩

private theorem field_prefix_rid (x : Input) :
    (((fields x.refund).take 4).flatMap (fun s=>segment s (fieldLen x s))).length=
      8+x.receipt.predecessorId.length+x.receipt.receiverId.length := by
  cases h : x.refund <;>
    simp [fields,h,fieldLen,segment_length,sCL,sPL,sP,sVL,sV] <;> omega

private theorem field_prefix_peoh (x : Input) :
    (((fields x.refund).take (17+(if x.refund then 1 else 0))).flatMap
      (fun s=>segment s (fieldLen x s))).length=
      144+32*(if x.refund then 1 else 0)+
        (x.receipt.predecessorId.length+x.receipt.receiverId.length+x.receipt.signerId.length+
          32*x.receipt.signerPk.tag) := by
  cases h : x.refund <;>
    simp [fields,h,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,
      sGP,sTL,sDEP,sXP0,sXRI,sXG,sXST,sXL0,sXLH] <;> omega

theorem receipt_rid_position (p : ReceiptPlan) (i : Nat) (hi : i<32) :
    (plannedReceiptRows p)[8+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length+i]?=
      some (.receipt p ⟨sRID,i,32⟩) := by
  have hh := field_lookup p.input (fields p.input.refund) 4 sRID i
    (by cases p.input.refund <;> rfl) (by simpa [fieldLen,sCL,sPL,sP,sVL,sV,sRID] using hi)
  rw [field_prefix_rid] at hh
  simp only [plannedReceiptRows,receiptRows,List.getElem?_map]
  rw [hh]
  rfl

theorem receipt_peoh_position (p : ReceiptPlan) (i : Nat) (hi : i<32) :
    (plannedReceiptRows p)[144+32*(if p.input.refund then 1 else 0)+
      (p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length+
        p.input.receipt.signerId.length+32*p.input.receipt.signerPk.tag)+i]?=
      some (.receipt p ⟨sXLH,i,32⟩) := by
  have hh := field_lookup p.input (fields p.input.refund)
    (17+(if p.input.refund then 1 else 0)) sXLH i
    (by cases p.input.refund <;> rfl)
    (by simpa [fieldLen,sCL,sPL,sP,sVL,sV,sRID,sT0,sSL,sS,sKT,sPK,
      sGP,sTL,sDEP,sXP0,sXRI,sXG,sXST,sXL0,sXLH] using hi)
  rw [field_prefix_peoh] at hh
  simp only [plannedReceiptRows,receiptRows,List.getElem?_map]
  rw [hh]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
