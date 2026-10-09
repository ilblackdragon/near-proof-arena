import ZkFormal.NearV3.Assembly.RcptStateHeaderCount

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem booleanReceiptTrace_header_reg (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ListPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.header p row)) (j : Nat) (hj : j<32) :
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos (reg j)=
      (headerStream own p).getD (row.index+j) 0 := by
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_other _ _ _ _ _ (reg j) (by change decide (31≤63+j ∧ 63+j≤42)=false; simp;omega)]
  unfold emittedReceiptBase nativeReceiptTrace
  rw [plannedTrace_cell lists log pos _ _ _ _ ha (reg j)]
  exact header_stream_reg own _ _ p row j hj

theorem booleanReceiptTrace_header_nj (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ListPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.header p row)) :
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos nj=Fp.ofNat p.inputs.length := by
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_other _ _ _ _ _ nj (by decide)]
  unfold emittedReceiptBase nativeReceiptTrace
  exact plannedTrace_cell lists log pos _ _ _ _ ha nj

theorem booleanReceiptTrace_headerCount (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hcount : ∀xs∈lists,xs.length<2^16) (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈headerCountConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    have hc : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos sCL=0 := by
      simpa only [ha] using booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback sCL (by decide)
    simp only [headerCountConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl <;> simp only [eval_mul3,eval_c,hc] <;> grind only
  | some a =>
    cases a with
    | receipt p row =>
      have hc := booleanReceiptTrace_receipt_not_header own ctx lists log pos constants pub digests fallback headerFallback p row ha
      simp only [headerCountConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl <;> simp only [eval_mul3,eval_c,hc] <;> grind only
    | header p row =>
      by_cases hi : row.index=0
      · have hn := hcount p.inputs (planned_header_inputs lists p row (List.mem_of_getElem? ha))
        obtain ⟨hb0,hb1,hb2⟩ := headerStream_count_small own p hn
        have hc := booleanReceiptTrace_header_reg own ctx lists log pos constants pub digests fallback headerFallback p row ha
        have hj := booleanReceiptTrace_header_nj own ctx lists log pos constants pub digests fallback headerFallback p row ha
        simp only [hi,Nat.zero_add] at hc
        simp only [headerCountConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl|rfl|rfl
        · simp only [eval_mul3,eval_sub,eval_add,eval_smul,eval_c,hj,hc 8 (by decide),hc 9 (by decide),hb0]
          grind only
        · simp only [eval_mul3,eval_c,hc 10 (by decide),hb1];grind only
        · simp only [eval_mul3,eval_c,hc 11 (by decide),hb2];grind only
      · have hf : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos fs=0 := by
          rw [booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback fs (by decide)]
          simp [ha,eraseRow,controlCell,fs,idx,act,hi]
        simp only [headerCountConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl|rfl|rfl <;> simp only [eval_mul3,eval_c,hf] <;> grind only

theorem booleanReceiptTrace_headerCount_native (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0) (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈headerCountConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 :=
  booleanReceiptTrace_headerCount own ctx lists (native_receipt_list_count lists hrun hgas)
    log pos constants pub digests fallback headerFallback

end ZkFormal.NearV3.Assembly.RcptSkeleton
