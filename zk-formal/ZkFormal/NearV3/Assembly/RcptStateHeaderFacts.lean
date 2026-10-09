import ZkFormal.NearV3.Assembly.RcptStateCheckpoint

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem planned_receipt_fields (lists : List (List Input)) (p : ReceiptPlan) (row : Coord)
    (hp : PlannedRow.receipt p row∈plannedRows lists) : row.state∈fields p.input.refund := by
  rw [←plannedSegments_rows] at hp
  obtain ⟨seg,hs,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hp
  obtain ⟨hstate,_,_⟩ := segment_member ha
  cases seg with
  | header lp => cases he
  | receipt rp s =>
    cases he
    change row.state=s at hstate
    rw [hstate]
    obtain ⟨lp,_,hs⟩ := List.mem_flatMap.mp hs
    simp only [listSegments,List.mem_cons] at hs
    rcases hs with hs|hs
    · cases hs
    · obtain ⟨rp,_,hs⟩ := List.mem_flatMap.mp hs
      obtain ⟨st,hst,he⟩ := List.mem_map.mp hs
      cases he
      exact hst

theorem fields_not_header (refund : Bool) : ∀s∈fields refund,s≠sCL := by
  cases refund <;> decide

theorem booleanReceiptTrace_receipt_not_header (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.receipt p row)) :
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos sCL=0 := by
  rw [booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback sCL (by decide)]
  have hs := fields_not_header p.input.refund row.state (planned_receipt_fields lists p row (List.mem_of_getElem? ha))
  simp only [ha,eraseRow]
  rw [control_state row (by decide : sCL∈states),if_neg (Ne.symm hs)]

theorem booleanReceiptTrace_header_values (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ListPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.header p row)) :
    let tr := booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback
    tr.cell 0 pos cj=0 ∧ tr.cell 0 pos oEnd=12 ∧ tr.cell 0 pos o2End=tr.cell 0 pos o2 ∧
    tr.cell 0 pos r=Fp.ofNat p.receiptIndex ∧ tr.cell 0 pos o2=Fp.ofNat p.bodyOffset := by
  dsimp only
  unfold booleanReceiptTrace emittedReceiptTrace
  have hc := plannedTrace_cell lists log pos (booleanConstants constants)
    (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux fallback))
    (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
      (emissionHeaderFallback (booleanHeaderAux headerFallback))) _ ha
  constructor
  · rw [emissionPatch_other _ _ _ _ _ cj (by decide)];exact hc cj
  constructor
  · rw [emissionPatch_other _ _ _ _ _ oEnd (by decide)];exact hc oEnd
  constructor
  · rw [emissionPatch_other _ _ _ _ _ o2End (by decide),emissionPatch_other _ _ _ _ _ o2 (by decide)]
    exact (hc o2End).trans (hc o2).symm
  constructor
  · rw [emissionPatch_other _ _ _ _ _ r (by decide)];exact hc r
  · rw [emissionPatch_other _ _ _ _ _ o2 (by decide)];exact hc o2

def headerCurrentConstraints : List Expr :=
  [.mul (c sCL) (c cj),.mul (c sCL) (sub (c oEnd) (k 12)),.mul (c sCL) (sub (c o2End) (c o2))]

theorem booleanReceiptTrace_headerCurrent (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈headerCurrentConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    have hc : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos sCL=0 := by
      simpa only [ha] using booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback sCL (by decide)
    simp only [headerCurrentConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl <;> simp only [eval_mul,eval_c,hc] <;> grind only
  | some a =>
    cases a with
    | header p row =>
      obtain ⟨hcj,hoe,ho2,_⟩ := booleanReceiptTrace_header_values own ctx lists log pos constants pub digests fallback headerFallback p row ha
      simp only [headerCurrentConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl <;> simp only [eval_mul,eval_sub,eval_c,eval_k,hcj,hoe,ho2] <;> grind only
    | receipt p row =>
      have hc := booleanReceiptTrace_receipt_not_header own ctx lists log pos constants pub digests fallback headerFallback p row ha
      simp only [headerCurrentConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl <;> simp only [eval_mul,eval_c,hc] <;> grind only

theorem headerCurrentConstraints_in_states : ∀e∈headerCurrentConstraints,e∈cStates := by
  intro e he
  simp only [headerCurrentConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cStates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
