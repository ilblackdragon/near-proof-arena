import ZkFormal.NearV3.Assembly.RcptGasTokenNativeBounds
import ZkFormal.NearV3.Assembly.RcptCurrentOwnedFamily

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasAccumulatorCurrent : List Expr :=
  [.mul gp (sub (.add (bitsX 31 8) (smul 256 (c (xb 39)))) (sum [c (tok 0),c burnt,c c4])),
   .mul (.mul gp (c fs)) (c c4),mul3 gp (c fe) (c (xb 39))]

theorem gasAccumulatorCurrent_footprint :
    gasAccumulatorCurrent.all currentExpr=true ∧ gasAccumulatorCurrent.all noEmissionExpr=true := by decide

theorem gasAccumulatorCurrent_mem : ∀e∈gasAccumulatorCurrent,e∈gasAccumulatorConstraints := by
  intro e he
  simp only [gasAccumulatorCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> simp [gasAccumulatorConstraints,cGas]

theorem gasAccumulatorCurrent_zero (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (hz : tr.cell t pos sGP=0) : ∀e∈gasAccumulatorCurrent,e.eval tr t pos pub=0 := by
  intro e he
  simp only [gasAccumulatorCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl
  all_goals simp only [gp,eval_mul,eval_mul3,eval_c,hz]
  all_goals grind only

theorem receipt_gasToken_current (tokens : ReceiptPlan→TokenInput)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hb : (tokens p).before+(tokens p).burnt<256^16)
    (hi : row.index<fieldLen p.input row.state) (hl : row.length=fieldLen p.input row.state) :
    ∀e∈gasAccumulatorCurrent,e.eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback))) p row row) 0 0 pub=0 := by
  by_cases hs : row.state=sGP
  · rw [hs] at hl hi
    change row.length=16 at hl
    change row.index<16 at hi
    cases row with
    | mk state index len =>
      dsimp only at hs hl hi
      subst state len
      intro e he
      have hh := receipt_gasToken_local tokens constants pub digests fallback p index hi hb
        ⟨sGP,index+1,16⟩ (fun _=>rfl) e (gasAccumulatorCurrent_mem e he)
      rw [currentExpr_eval _ (receiptPair (booleanConstants constants)
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback))) p
        ⟨sGP,index,16⟩ ⟨sGP,index+1,16⟩) 0 0 0 0 pub (by intro col;rfl) e
        (List.all_eq_true.mp gasAccumulatorCurrent_footprint.1 e he)]
      exact hh
  · apply gasAccumulatorCurrent_zero
    have hh := (receipt_control_cell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasTokenAux tokens fallback))) p row (show controlColumn sGP=true by decide)).trans
      (control_state row (show sGP∈states by decide))
    exact hh.trans (if_neg (Ne.symm hs))

theorem booleanReceiptTrace_gasTokenCurrent (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈gasAccumulatorCurrent,e.eval (booleanReceiptTrace own ctx lists log constants
      pub digests (gasTokenAux (receiptPlanToken ctx lists) fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp gasAccumulatorCurrent_footprint.2 e he)]
  apply plannedTrace_current_owned_family lists log pos _ _ _ pub gasAccumulatorCurrent gasAccumulatorCurrent_footprint.1 ?_ ?_ ?_ e he
  · intro p row hm hl hi
    exact receipt_gasToken_current (receiptPlanToken ctx lists) constants pub digests fallback p row
      (planned_receipt_token_bound ctx lists p row hm hrun) hi hl
  · intro p i
    exact gasAccumulatorCurrent_zero _ _ _ _ rfl
  · exact gasAccumulatorCurrent_zero _ _ _ _ rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
