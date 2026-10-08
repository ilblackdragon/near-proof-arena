import ZkFormal.NearV3.Assembly.RcptNamedArithmetic

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

def namedEndConstraints : List Expr :=
  [mul3 (c sV) (c fe) (sub (c p1) (.add (sq (sub (c Lv) (k 64))) (sq (sub (c acc) (c Lv))))),
   mul3 (c sV) (c fe) (sub (c p2) (sum [sq (sub (c Lv) (k 42)),sq (sub (c vc0) (k 48)),
     sq (sub (c vc1) (k 120)),sq (sub (sub (c acc) (c h01)) (k 40))])),
   mul3 (c sV) (c fe) (sub (c p3) (sum [sq (sub (c Lv) (k 42)),sq (sub (c vc0) (k 48)),
     sq (sub (c vc1) (k 115)),sq (sub (sub (c acc) (c h01)) (k 40))]))]

theorem namedEnd_in_chars : ∀e∈namedEndConstraints,e∈cChars := by
  intro e he
  simp only [namedEndConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cChars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem namedEnd_footprint : namedEndConstraints.all currentExpr=true ∧
    namedEndConstraints.all noEmissionExpr=true := by decide

theorem namedEnd_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sV=0 ∨ tr.cell 0 pos fe=0) :
    ∀e∈namedEndConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [namedEndConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> simp only [eval_mul3,eval_c]
  all_goals rcases hz with hz|hz <;> rw [hz] <;> grind only

set_option maxRecDepth 4096 in
theorem receipt_named_end (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hlen : row.length=fieldLen p.input row.state) :
    ∀e∈namedEndConstraints,e.eval
      (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (namedAux fallback))) p row row)
      0 0 pub=0 := by
  let cn := booleanConstants constants
  let aux := tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (namedAux fallback))
  let tr := receiptPair cn aux p row row
  change ∀e∈namedEndConstraints,e.eval tr 0 0 pub=0
  by_cases hs : row.state=sV
  · by_cases he : row.index+1=row.length
    · have hi : row.index+1=p.input.receipt.receiverId.length := by
        simpa [hlen,hs,fieldLen,sV,sP,sCL,sPL,sVL] using he
      have hh := named_score_end p.input.receipt row.index hi
      have hcells : ∀col,col∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]→
          tr.cell 0 0 col=namedAux fallback p row col :=
        namedAux_transport ctx lists constants pub digests fallback p row
      have hlv : tr.cell 0 0 Lv=Fp.ofNat p.input.receipt.receiverId.length := rfl
      intro e he
      simp only [namedEndConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl
      all_goals
        simp only [eval_mul3,eval_sub,eval_add,eval_c,eval_k,sq,eval_mul,eval_sum_cons,eval_sum_nil,hlv]
        first | rw [hcells p1 (by decide)] | rw [hcells p2 (by decide)] | rw [hcells p3 (by decide)]
        simp only [hcells acc (by decide),hcells vc0 (by decide),hcells vc1 (by decide),hcells h01 (by decide)]
        simp only [namedAux,hs,acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3,Nat.reduceEqDiff,↓reduceIte]
        grind only
    · apply namedEnd_zero
      apply Or.inr
      change (if row.index+1=row.length then (1:Fp) else 0)=0
      exact if_neg he
  · apply namedEnd_zero
    apply Or.inl
    exact (receipt_control_cell cn aux p row (show controlColumn sV=true by decide)).trans
      ((control_state row (show sV∈states by decide)).trans (if_neg (Ne.symm hs)))

theorem booleanReceiptTrace_namedEnd (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈namedEndConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests (namedAux fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp namedEnd_footprint.2 e he)]
  apply plannedTrace_current_family lists hw log pos _ _ _ pub namedEndConstraints namedEnd_footprint.1
    (fun p row _ hlen=>receipt_named_end ctx lists constants pub digests fallback p row hlen) ?_ ?_ e he
  · intro p i
    apply namedEnd_zero
    exact Or.inl rfl
  · apply namedEnd_zero
    exact Or.inl rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
