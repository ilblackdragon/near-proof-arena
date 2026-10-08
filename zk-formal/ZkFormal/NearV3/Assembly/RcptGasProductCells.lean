import ZkFormal.NearV3.Assembly.RcptGasProductLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem gasBorrow_product_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (gasProductAux ctx fallback)=gasProductAux ctx (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute (gasProductAux ctx)
  · intro a b p row col he;simp only [gasProductAux,he]
  · intro a p row col hs hc
    have hn : col≠ramt ∧ col≠c2 ∧ col≠c3 ∧ ¬(xb 9≤col ∧ col<xb 20) ∧ ¬(xb 20≤col ∧ col<xb 31) := by
      simp only [c1,xb] at hc
      simp only [ramt,c2,c3,xb]
      omega
    simp only [gasProductAux,hs,ite_true,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,ite_false]

theorem gasEffective_product_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (gasProductAux ctx fallback)=gasProductAux ctx (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (gasProductAux ctx)
  · intro a b p row col he;simp only [gasProductAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem candidateGasDelay_product_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    candidateGasDelayAux ctx (gasProductAux ctx fallback)=gasProductAux ctx (candidateGasDelayAux ctx fallback) := by
  funext p row col
  by_cases hs : row.state=sGP
  · by_cases hd : dl 0≤col ∧ col<dl 8
    · have hn : col≠ramt ∧ col≠c2 ∧ col≠c3 ∧ ¬(xb 9≤col ∧ col<xb 20) ∧ ¬(xb 20≤col ∧ col<xb 31) := by
        simp only [dl] at hd
        simp only [ramt,c2,c3,xb];omega
      simp only [candidateGasDelayAux,gasProductAux,hs,hd.1,hd.2,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,ite_true,ite_false,true_and]
    · simp only [candidateGasDelayAux,gasProductAux,hs,true_and,hd,ite_false,ite_true]
  · simp only [candidateGasDelayAux,gasProductAux,hs,false_and,ite_false]

theorem gasProduct_burn_bits (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) (next : Coord) :
    (bitsX 9 11).eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasProductAux ctx fallback)))
      p ⟨sGP,i,len⟩ next) 0 0 pub=Fp.ofNat (gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)) := by
  have hbound : gasMulCarry (gasBurnPrice ctx p.input.receipt) (i+1)<2^11 := by
    have h := gasMulCarry_le (gasBurnPrice ctx p.input.receipt) (i+1);omega
  rw [← Nat.mod_eq_of_lt hbound]
  apply eval_frame_bits
  intro j hj
  exact gasProduct_burn_bit ctx constants pub digests tokens fallback p i len j hj

theorem gasProduct_surplus_bits (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp)
    (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp) (tokens : ReceiptPlan→TokenInput)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (i len : Nat) (next : Coord) :
    (bitsX 20 11).eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasProductAux ctx fallback)))
      p ⟨sGP,i,len⟩ next) 0 0 pub=Fp.ofNat (gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)) := by
  have hbound : gasMulCarry (gasSurplusPrice ctx p.input.receipt) (i+1)<2^11 := by
    have h := gasMulCarry_le (gasSurplusPrice ctx p.input.receipt) (i+1);omega
  rw [← Nat.mod_eq_of_lt hbound]
  apply eval_frame_bits
  intro j hj
  exact gasProduct_surplus_bit ctx constants pub digests tokens fallback p i len j hj

end ZkFormal.NearV3.Assembly.RcptSkeleton
