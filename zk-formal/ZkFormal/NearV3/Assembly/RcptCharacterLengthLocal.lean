import ZkFormal.NearV3.Assembly.RcptCharacterLengths

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

set_option maxHeartbeats 2000000 in
theorem receipt_character_length_pair (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hw : p.input.receipt.wf=true) (s col : Nat) (hs : s∈[sP,sV,sS])
    (hlen : receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterLengthAux fallback)))
        p row col=Fp.ofNat (characterBytes p.input s).length) :
    let tr := receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterLengthAux fallback))) p row row
    (mul3 (c fe) (c s) (sub (sub (c col) (k 2)) (bitsX 0 6))).eval tr 0 0 pub=0 ∧
    (mul3 (c fe) (c s) (sub (sub (k 64) (c col)) (bitsX 6 6))).eval tr 0 0 pub=0 := by
  dsimp only
  have hsc : controlColumn s=true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl <;> decide
  have hstates : s∈states := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl <;> decide
  have hst := (receipt_control_cell (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterLengthAux fallback))) p row hsc).trans
      (control_state row hstates)
  by_cases he : s=row.state
  · have hrow : row.state∈[sP,sV,sS] := he ▸ hs
    have hb := characterBytes_bounds p.input hw row.state hrow
    have h0 := eval_frame_bits
      (receiptPair (booleanConstants constants)
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterLengthAux fallback))) p row row)
      0 0 pub 0 ((characterBytes p.input row.state).length-2) 6
      (fun i hi=>by simpa only [Nat.zero_add,receiptPair,ite_self] using (characterLength_bit_cells ctx lists constants pub digests fallback p row hrow i hi).1)
    have h6 := eval_frame_bits
      (receiptPair (booleanConstants constants)
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterLengthAux fallback))) p row row)
      0 0 pub 6 (64-(characterBytes p.input row.state).length) 6
      (fun i hi=>by simpa only [receiptPair,ite_self] using (characterLength_bit_cells ctx lists constants pub digests fallback p row hrow i hi).2)
    rw [Nat.mod_eq_of_lt (by omega)] at h0 h6
    have hlo := congrArg (fun n:Nat=>(n:Fp)) (Nat.sub_add_cancel hb.1)
    have hhi := congrArg (fun n:Nat=>(n:Fp)) (Nat.sub_add_cancel hb.2)
    have hlen' : (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterLengthAux fallback))) p row row).cell 0 0 col=
        Fp.ofNat (characterBytes p.input row.state).length := by simpa only [he,receiptPair,ite_self] using hlen
    constructor
    · simp only [eval_mul3,eval_sub,eval_c,eval_k,hlen',h0]
      change _*((((characterBytes p.input row.state).length:Fp)-2)-((characterBytes p.input row.state).length-2:Nat))=0
      grind only
    · simp only [eval_mul3,eval_sub,eval_c,eval_k,hlen',h6]
      change _*((64-((characterBytes p.input row.state).length:Fp))-(64-(characterBytes p.input row.state).length:Nat))=0
      grind only
  · constructor <;> simp only [eval_mul3,eval_c,receiptPair,ite_self,hst,if_neg he] <;> grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
