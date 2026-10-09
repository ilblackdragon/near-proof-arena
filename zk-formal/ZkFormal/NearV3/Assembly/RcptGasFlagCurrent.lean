import ZkFormal.NearV3.Assembly.RcptGasFlagLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasFlagCurrent : List Expr :=
  [.mul (mul3 gp (Dsl.not (c hr)) (c gq)) DE,
   mul3 gp (c fs) (sub (c sumD) DE),
   mul3 gp (c fe) (sub (.mul (c sumD) (c invA)) (c hr))]

theorem gasFlagCurrent_footprint :
    gasFlagCurrent.all currentExpr=true ∧ gasFlagCurrent.all noEmissionExpr=true := by decide

theorem gasFlagCurrent_mem : ∀e∈gasFlagCurrent,e∈gasFlagConstraints := by
  intro e he
  simp only [gasFlagCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> simp [gasFlagConstraints,cGas]

theorem gasFlagCurrent_zero (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (hz : tr.cell t pos sGP=0) : ∀e∈gasFlagCurrent,e.eval tr t pos pub=0 := by
  intro e he
  simp only [gasFlagCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl
  all_goals simp only [gp,eval_mul,eval_mul3,eval_c,hz]
  all_goals grind only

theorem receipt_gasFlag_current (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hf : p.input.refund=nativeRefund ctx p.input.receipt)
    (hw : p.input.receipt.wf=true) (hi : row.index<fieldLen p.input row.state)
    (hl : row.length=fieldLen p.input row.state) (hc : ctx.gasPrice<256^16) :
    ∀e∈gasFlagCurrent,e.eval (receiptPair (booleanConstants (gasEffectiveConstants ctx constants))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasFlagAux ctx (gasBorrowAux ctx fallback)))) p row row) 0 0 pub=0 := by
  by_cases hs : row.state=sGP
  · have hr : p.input.receipt.gasPrice<256^16 := by
      simp only [Receipt.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
      have hh : p.input.receipt.gasPrice<Params.two128 := hw.1.2
      exact hh
    rw [hs] at hl hi
    change row.length=16 at hl
    change row.index<16 at hi
    cases row with
    | mk state index len =>
      dsimp only at hs hl hi
      subst state len
      intro e he
      have hh := receipt_gasFlag_local ctx constants pub digests tokens fallback p index hi hf hr hc
        ⟨sGP,index+1,16⟩ (fun _=>rfl) e (gasFlagCurrent_mem e he)
      rw [currentExpr_eval _ (receiptPair (booleanConstants (gasEffectiveConstants ctx constants))
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasFlagAux ctx (gasBorrowAux ctx fallback)))) p
        ⟨sGP,index,16⟩ ⟨sGP,index+1,16⟩) 0 0 0 0 pub (by intro col;rfl) e
        (List.all_eq_true.mp gasFlagCurrent_footprint.1 e he)]
      exact hh
  · apply gasFlagCurrent_zero
    have hh := (receipt_control_cell (booleanConstants (gasEffectiveConstants ctx constants))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasFlagAux ctx (gasBorrowAux ctx fallback)))) p row (show controlColumn sGP=true by decide)).trans
      (control_state row (show sGP∈states by decide))
    exact hh.trans (if_neg (Ne.symm hs))

theorem booleanReceiptTrace_gasFlagCurrent (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hf : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hc : ctx.gasPrice<256^16) :
    ∀e∈gasFlagCurrent,e.eval (booleanReceiptTrace own ctx lists log (gasEffectiveConstants ctx constants)
      pub digests (gasFlagAux ctx (gasBorrowAux ctx fallback)) headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp gasFlagCurrent_footprint.2 e he)]
  apply plannedTrace_current_bounded_family lists hw log pos _ _ _ pub gasFlagCurrent gasFlagCurrent_footprint.1
    ?_ ?_ ?_ e he
  · intro p row hm hw hl hi
    obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hm
    exact receipt_gasFlag_current ctx constants pub digests (receiptPlanToken ctx lists) fallback p row (hf xs hxs p.input hx) hw hi hl hc
  · intro p i
    exact gasFlagCurrent_zero _ _ _ _ rfl
  · exact gasFlagCurrent_zero _ _ _ _ rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
