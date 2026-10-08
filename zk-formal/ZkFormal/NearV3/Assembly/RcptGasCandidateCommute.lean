import ZkFormal.NearV3.Assembly.RcptGasProductCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem gasToken_candidateDelay_commute (tokens : ReceiptPlan→TokenInput) (ctx : ApplyCtx)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (candidateGasDelayAux ctx fallback)=candidateGasDelayAux ctx (gasTokenAux tokens fallback) := by
  apply gasToken_commute (candidateGasDelayAux ctx)
  · intro a b p row col he
    simp only [candidateGasDelayAux,he]
  · intro a p row col hs hc
    have hn : ¬(dl 0≤col ∧ col<dl 8) := by simp only [burnt,c4,xb] at hc;simp only [dl];omega
    simp only [candidateGasDelayAux,hs,hn,true_and,ite_false]

theorem gasFlag_candidateDelay_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (candidateGasDelayAux ctx fallback)=candidateGasDelayAux ctx (gasFlagAux ctx fallback) := by
  apply gasFlag_commute (candidateGasDelayAux ctx)
  · intro a b p row col he
    simp only [candidateGasDelayAux,he]
  · intro a p row col hs hc
    have hn : ¬(dl 0≤col ∧ col<dl 8) := by simp only [sumD,invA] at hc;simp only [dl];omega
    simp only [candidateGasDelayAux,hs,hn,true_and,ite_false]

theorem gasToken_product_commute (tokens : ReceiptPlan→TokenInput) (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (gasProductAux ctx fallback)=gasProductAux ctx (gasTokenAux tokens fallback) := by
  apply gasToken_commute (gasProductAux ctx)
  · intro a b p row col he;simp only [gasProductAux,he]
  · intro a p row col hs hc
    have hn : col≠ramt ∧ col≠c2 ∧ col≠c3 ∧ ¬(xb 9≤col ∧ col<xb 20) ∧ ¬(xb 20≤col ∧ col<xb 31) := by
      simp only [burnt,c4,xb] at hc
      simp only [ramt,c2,c3,xb];omega
    simp only [gasProductAux,hs,ite_true,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,ite_false]

theorem gasFlag_product_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (gasProductAux ctx fallback)=gasProductAux ctx (gasFlagAux ctx fallback) := by
  apply gasFlag_commute (gasProductAux ctx)
  · intro a b p row col he;simp only [gasProductAux,he]
  · intro a p row col hs hc
    have hn : col≠ramt ∧ col≠c2 ∧ col≠c3 ∧ ¬(xb 9≤col ∧ col<xb 20) ∧ ¬(xb 20≤col ∧ col<xb 31) := by
      simp only [sumD,invA] at hc
      simp only [ramt,c2,c3,xb];omega
    simp only [gasProductAux,hs,ite_true,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,ite_false]

end ZkFormal.NearV3.Assembly.RcptSkeleton
