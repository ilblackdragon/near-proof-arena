import ZkFormal.NearV3.Assembly.RcptGasBorrowLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def gasBorrowCurrent : List Expr :=
  [ .mul gp (sub (sub (c b) (c (reg 0))) (sub (.add (c c1) DE) (smul 256 (c (xb 8))))),
    .mul (.mul gp (c fs)) (c c1),
    mul3 gp (c fe) (sub (c (xb 8)) (Dsl.not (c ge))) ]

theorem gasBorrowCurrent_footprint :
    gasBorrowCurrent.all currentExpr=true ∧ gasBorrowCurrent.all noEmissionExpr=true := by decide

theorem gasBorrowCurrent_mem : ∀e∈gasBorrowCurrent,e∈gasBorrowConstraints := by
  intro e he
  simp only [gasBorrowCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> simp [gasBorrowConstraints]

theorem gasBorrowCurrent_zero (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (hz : tr.cell t pos sGP=0) : ∀e∈gasBorrowCurrent,e.eval tr t pos pub=0 := by
  intro e he
  simp only [gasBorrowCurrent,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl
  all_goals simp only [gp,eval_mul,eval_mul3,eval_c,hz]
  all_goals grind only

theorem receipt_gasBorrow_current (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (hpub : GasPublicBytes ctx pub)
    (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hw : p.input.receipt.wf=true) (hi : row.index<fieldLen p.input row.state)
    (hl : row.length=fieldLen p.input row.state) (hc : ctx.gasPrice<256^16) :
    ∀e∈gasBorrowCurrent,e.eval (receiptPair (booleanConstants (nativePriceConstants ctx constants))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasBorrowAux ctx fallback))) p row row) 0 0 pub=0 := by
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
      have hh := receipt_gasBorrow_local ctx constants pub hpub digests tokens fallback p index hi
        ⟨sGP,index+1,16⟩ (fun _=>rfl) hr hc e (gasBorrowCurrent_mem e he)
      rw [currentExpr_eval _ (receiptPair (booleanConstants (nativePriceConstants ctx constants))
        (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasBorrowAux ctx fallback))) p
        ⟨sGP,index,16⟩ ⟨sGP,index+1,16⟩) 0 0 0 0 pub (by intro col;rfl) e
        (List.all_eq_true.mp gasBorrowCurrent_footprint.1 e he)]
      exact hh
  · apply gasBorrowCurrent_zero
    have hh := (receipt_control_cell (booleanConstants (nativePriceConstants ctx constants))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasBorrowAux ctx fallback))) p row (show controlColumn sGP=true by decide)).trans
      (control_state row (show sGP∈states by decide))
    exact hh.trans (if_neg (Ne.symm hs))

theorem booleanReceiptTrace_gasBorrowCurrent (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (hpub : GasPublicBytes ctx pub)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hc : ctx.gasPrice<256^16) :
    ∀e∈gasBorrowCurrent,e.eval (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx constants)
      pub digests (gasBorrowAux ctx fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp gasBorrowCurrent_footprint.2 e he)]
  apply plannedTrace_current_bounded_family lists hw log pos _ _ _ pub gasBorrowCurrent gasBorrowCurrent_footprint.1
    (fun p row _ hw hl hi=>receipt_gasBorrow_current ctx constants pub hpub digests (receiptPlanToken ctx lists) fallback p row hw hi hl hc) ?_ ?_ e he
  · intro p i
    exact gasBorrowCurrent_zero _ _ _ _ rfl
  · exact gasBorrowCurrent_zero _ _ _ _ rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
