import ZkFormal.NearV3.Assembly.RcptBooleanLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem currentControl_eval (tr tr' : Trace Fp) (t r t' r' : Nat) (pub : List Fp)
    (hc : ∀c,controlColumn c=true→tr.cell t r c=tr'.cell t' r' c)
    (e : Expr) (he : controlExpr e=true) (hec : currentExpr e=true) :
    e.eval tr t r pub=e.eval tr' t' r' pub := by
  induction e with
  | const => rfl
  | pub => rfl
  | col c nx => cases nx with | false=>exact hc c he | true=>cases hec
  | isFirst | isLast | isTransition => cases he
  | add a b ia ib =>
    have hs : controlExpr a=true ∧ controlExpr b=true := by simpa only [controlExpr,Bool.and_eq_true] using he
    have hc : currentExpr a=true ∧ currentExpr b=true := by simpa only [currentExpr,Bool.and_eq_true] using hec
    simp only [eval_add,ia hs.1 hc.1,ib hs.2 hc.2]
  | mul a b ia ib =>
    have hs : controlExpr a=true ∧ controlExpr b=true := by simpa only [controlExpr,Bool.and_eq_true] using he
    have hc : currentExpr a=true ∧ currentExpr b=true := by simpa only [currentExpr,Bool.and_eq_true] using hec
    simp only [eval_mul,ia hs.1 hc.1,ib hs.2 hc.2]
  | neg a ia => simp only [eval_neg,ia he hec]

theorem plannedCell_control (constants : ReceiptPlan→Nat→Fp)
    (receiptAux : ReceiptPlan→Coord→Nat→Fp) (headerAux : ListPlan→Coord→Nat→Fp)
    (a : PlannedRow) (col : Nat) (hc : controlColumn col=true) :
    plannedCell constants receiptAux headerAux a col=controlCell (eraseRow a) col := by
  cases a with
  | header p row => exact header_control_cell _ _ _ hc
  | receipt p row => exact receipt_control_cell _ _ _ _ hc

def oneHotConstraint : Expr := sub (sum (states.map c)) (c act)

set_option maxRecDepth 4096 in
theorem oneHotConstraint_footprint : controlExpr oneHotConstraint=true ∧ currentExpr oneHotConstraint=true := by decide

set_option maxRecDepth 4096 in
theorem controlColumn_noEmission : ∀col,controlColumn col=true→emissionColumn col=false := by
  intro col hc
  simp only [controlColumn,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hc
  simp only [emissionColumn,decide_eq_false_iff_not]
  omega

theorem booleanReceiptTrace_control (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (col : Nat) (hc : controlColumn col=true) :
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos col=
      match (plannedRows lists)[pos]? with | none=>0 | some a=>controlCell (eraseRow a) col := by
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_other _ _ _ _ _ _ (controlColumn_noEmission col hc)]
  unfold emittedReceiptBase nativeReceiptTrace
  cases ha : (plannedRows lists)[pos]? with
  | none => exact plannedTrace_padding lists log pos _ _ _ (List.getElem?_eq_none_iff.mp ha) col
  | some a =>
    rw [plannedTrace_cell lists log pos _ _ _ a ha col]
    exact plannedCell_control _ _ _ a col hc

theorem zeroControl_sum (tr : Trace Fp) (pos : Nat) (pub : List Fp) :
    ∀cs : List Nat,(∀col∈cs,tr.cell 0 pos col=0)→(sum (cs.map c)).eval tr 0 pos pub=0
  | [],_=>rfl
  | col::cs,h=>by
    simp only [List.map_cons,eval_sum_cons,eval_c,h col (by simp)]
    rw [zeroControl_sum tr pos pub cs (fun x hx=>h x (by simp [hx]))]
    grind only

theorem booleanReceiptTrace_oneHot (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    oneHotConstraint.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    simp only [ha] at hc
    have hz : ∀col∈states,(booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos col=0 := by
      intro col hm
      have hl := states_limits hm
      exact hc col (by simp [controlColumn];omega)
    simp only [oneHotConstraint,eval_sub,zeroControl_sum _ _ _ states hz,eval_c,hc act (by decide)]
    grind only
  | some a =>
    simp only [ha] at hc
    rw [currentControl_eval _ (controlPair (eraseRow a) (eraseRow a)) 0 pos 0 0 pub
      (fun col hm=>hc col hm) _ oneHotConstraint_footprint.1 oneHotConstraint_footprint.2]
    simp only [oneHotConstraint,eval_sub,control_onehot _ _ (planned_row_state lists a (List.mem_of_getElem? ha)) pub,eval_c]
    change (1:Fp)-1=0
    grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
