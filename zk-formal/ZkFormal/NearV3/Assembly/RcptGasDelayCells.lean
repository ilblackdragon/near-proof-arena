import ZkFormal.NearV3.Assembly.RcptGasDelayFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem gasBorrow_delay_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (gasDelayAux ctx fallback)=gasDelayAux ctx (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute (gasDelayAux ctx)
  · intro a b p row col he
    simp only [gasDelayAux,he]
  · intro a p row col hs hc
    have hn : ¬(row.state=sGP ∧ dl 0≤col ∧ col<dl 8) := by
      simp only [c1,xb] at hc
      simp only [dl]
      omega
    simp only [gasDelayAux,if_neg hn]

theorem gasEffective_delay_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (gasDelayAux ctx fallback)=gasDelayAux ctx (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (gasDelayAux ctx)
  · intro a b p row col he
    simp only [gasDelayAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem gasDelay_pc_cell (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux
        (gasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx fallback))))) p ⟨sGP,i,len⟩ pc=
      Fp.ofNat (gasEffectiveByte ctx p.input.receipt i) := rfl

theorem gasDelay_difference_eval (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) (next : Coord) :
    DE.eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux
        (gasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx fallback))))) p ⟨sGP,i,len⟩ next) 0 0 pub=
      Fp.ofNat (gasDifference ctx p.input.receipt i) := by
  simpa only [gasBorrow_delay_commute,←gasEffective_borrow_commute] using
    gasDifference_eval ctx constants pub digests tokens (gasDelayAux ctx (gasEffectiveAux ctx fallback)) p i len next

theorem gasDelay_surplus_eval (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) (next : Coord) :
    surE.eval (receiptPair (booleanConstants (nativePriceConstants ctx constants))
      (tokenReceiptAux pub digests tokens (booleanReceiptAux
        (gasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx fallback))))) p ⟨sGP,i,len⟩ next) 0 0 pub=
      Fp.ofNat (gasRawSurplusByte ctx p.input.receipt i) := by
  let tr := receiptPair (booleanConstants (nativePriceConstants ctx constants))
    (tokenReceiptAux pub digests tokens (booleanReceiptAux
      (gasDelayAux ctx (gasEffectiveAux ctx (gasBorrowAux ctx fallback))))) p ⟨sGP,i,len⟩ next
  have hg : tr.cell 0 0 ge=bitCell (decide (ctx.gasPrice≤p.input.receipt.gasPrice)) := by
    change boolInput ge (bitCell _)=_
    exact boolInput_preserves _ _ (bitCell_boolean _)
  change surE.eval tr 0 0 pub=_
  simp only [surE,eval_mul,eval_c,hg]
  rw [gasDelay_difference_eval]
  by_cases h : ctx.gasPrice≤p.input.receipt.gasPrice
  all_goals simp only [gasRawSurplusByte,h,decide_true,decide_false,bitCell,Bool.false_eq_true,ite_true,ite_false,show Fp.ofNat 0=(0:Fp) from rfl]
  all_goals grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
