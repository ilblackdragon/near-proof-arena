import ZkFormal.NearV3.Rcpt.Candidates.ReceiptJobOrder
import ZkFormal.NearV3.Candidates.NativeAccessKeyOrder
import ZkFormal.NearV3.Candidates.NativeReceiptLocationLayout
import ZkFormal.NearV3.Assembly.RcptCandidateAccessTraffic
namespace ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton ZkFormal.Air ZkFormal.Algebra RcptV3Proof RcptV3

private theorem zip_ignore (xs : List RcptE) (f : RcptE→List Msg) (n : Nat) :
    (xs.zipIdx n).flatMap (fun p=>f p.1)=xs.flatMap f := by
  induction xs generalizing n with
  | nil=>rfl
  | cons x xs ih=>simp only [List.zipIdx_cons,List.flatMap_cons,ih]

theorem access_view_flat (pub : List Fp) (ls : RcptV3Vs) (sd : Bool) :
    (if sd then rcptSends3 pub ls B_AKC else rcptRecvs3 ls B_AKC)=
      (flatR ls).flatMap (ReceiptCandidateProof.accessCounterMsgs sd 0) := by
  have h:=Rcpt.Candidates.located_global_order ls 0 (ReceiptCandidateProof.accessCounterMsgs sd)
  have hignore:(flatR ls).zipIdx.flatMap (fun p=>ReceiptCandidateProof.accessCounterMsgs sd p.2 p.1)=
      (flatR ls).flatMap (ReceiptCandidateProof.accessCounterMsgs sd 0):=zip_ignore _ _ 0
  rw [hignore] at h
  rw [←h]
  cases sd <;> simp only [ite_true,Bool.false_eq_true,ite_false,rcptSends3,rcptRecvs3,
    show B_AKC≠B_BYTES by decide,show B_AKC≠B_RCL by decide,List.nil_append]
  all_goals
    apply ZkFormal.Near.Render.flatMap_congr'
    intro j _
    apply ZkFormal.Near.Render.flatMap_congr'
    intro x _
    simp [rSends,rRecvs,ReceiptCandidateProof.accessCounterMsgs,B_AKC,B_BYTES,B_KEYNIB,B_MEM,B_RIDS,B_MPOS,B_SREC,B_DIGEST,B_FINAL]

theorem receipt_t0_position (p : ReceiptPlan) :
    (plannedReceiptRows p)[40+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length]?=
      some (.receipt p ⟨sT0,0,1⟩) := by
  have hh:=field_lookup p.input (fields p.input.refund) 5 sT0 0
    (by cases p.input.refund <;> rfl) (by change 0<1;decide)
  have hp:(((fields p.input.refund).take 5).flatMap (fun s=>segment s (fieldLen p.input s))).length=
      40+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length:=by
    cases p.input.refund <;> simp [fields,fieldLen,segment_length,sCL,sPL,sP,sVL,sV,sRID,sT0] <;> omega
  rw [hp] at hh
  simp only [plannedReceiptRows,receiptRows,List.getElem?_map]
  rw [show 40+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length=40+p.input.receipt.predecessorId.length+p.input.receipt.receiverId.length+0 by omega,hh]
  rfl
end ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
