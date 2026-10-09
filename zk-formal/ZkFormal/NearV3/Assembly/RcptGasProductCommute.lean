import ZkFormal.NearV3.Assembly.RcptCandidateGasDelayCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem gasProduct_commute (F : (ReceiptPlan→Coord→Nat→Fp)→ReceiptPlan→Coord→Nat→Fp)
    (hlocal : ∀a b p row col,a p row col=b p row col→F a p row col=F b p row col)
    (hfree : ∀a p row col,row.state=sGP→
      (col=ramt ∨ col=c2 ∨ col=c3 ∨ (xb 9≤col ∧ col<xb 31))→F a p row col=a p row col)
    (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (F fallback)=F (gasProductAux ctx fallback) := by
  funext p row col
  by_cases hs : row.state=sGP
  · by_cases hc : col=ramt ∨ col=c2 ∨ col=c3 ∨ (xb 9≤col ∧ col<xb 31)
    · rw [hfree _ p row col hs hc]
      simp only [gasProductAux,hfree fallback p row col hs hc]
    · have hn : col≠ramt ∧ col≠c2 ∧ col≠c3 ∧ ¬(xb 9≤col ∧ col<xb 20) ∧ ¬(xb 20≤col ∧ col<xb 31) := by
        simp only [xb] at hc ⊢;omega
      have he (a : ReceiptPlan→Coord→Nat→Fp) : gasProductAux ctx a p row col=a p row col := by
        simp only [gasProductAux,hs,ite_true,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,ite_false]
      rw [he]
      exact (hlocal _ _ p row col (he fallback)).symm
  · have he (a : ReceiptPlan→Coord→Nat→Fp) : gasProductAux ctx a p row col=a p row col := by
      simp only [gasProductAux,hs,ite_false]
    rw [he]
    exact (hlocal _ _ p row col (he fallback)).symm

theorem gasProduct_digest_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (digestMetadata fallback)=digestMetadata (gasProductAux ctx fallback) := by
  apply gasProduct_commute digestMetadata
  · intro a b p row col he
    simp only [digestMetadata,he]
  · intro a p row col hs hc
    have hn : col≠gDg ∧ col≠dI ∧ col≠dL := by
      simp only [ramt,c2,c3,xb] at hc
      simp only [gDg,dI,dL]
      omega
    rcases hn with ⟨h0,h1,h2⟩
    simp only [digestMetadata,if_neg h0,if_neg h1,if_neg h2,ite_self]

theorem gasProduct_system_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (systemAux fallback)=systemAux (gasProductAux ctx fallback) := by
  apply gasProduct_commute systemAux
  · intro a b p row col he
    simp only [systemAux,he]
  · intro a p row col hs hc
    have hn : col≠gV ∧ col≠gS ∧ col≠sx ∧ col≠invD ∧ col≠scnt ∧ col≠invL := by
      simp only [ramt,c2,c3,xb] at hc
      simp only [gV,gS,sx,invD,scnt,invL]
      omega
    rcases hn with ⟨h0,h1,h2,h3,h4,h5⟩
    simp only [systemAux,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,ite_self]

theorem gasProduct_length_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (characterLengthAux fallback)=characterLengthAux (gasProductAux ctx fallback) := by
  apply gasProduct_commute characterLengthAux
  · intro a b p row col he
    simp only [characterLengthAux,he]
  · intro a p row col hs hc
    simp only [characterLengthAux,hs,List.mem_cons,List.not_mem_nil,or_false,sGP,sP,sV,sS,Nat.reduceEqDiff,false_or,ite_false]

theorem gasProduct_predecessor_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (predecessorAux fallback)=predecessorAux (gasProductAux ctx fallback) := by
  apply gasProduct_commute predecessorAux
  · intro a b p row col he
    simp only [predecessorAux,he]
  · intro a p row col hs hc
    simp only [predecessorAux,hs,sGP,sP,Nat.reduceEqDiff,ite_false]

theorem gasProduct_named_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (namedAux fallback)=namedAux (gasProductAux ctx fallback) := by
  apply gasProduct_commute namedAux
  · intro a b p row col he
    simp only [namedAux,he]
  · intro a p row col hs hc
    simp only [namedAux,hs,sGP,sV,Nat.reduceEqDiff,ite_false]

theorem gasProduct_character_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (characterAux fallback)=characterAux (gasProductAux ctx fallback) := by
  apply gasProduct_commute characterAux
  · intro a b p row col he
    simp only [characterAux,he]
  · intro a p row col hs hc
    have hn : ¬(111≤col ∧ col≤123) := by simp only [ramt,c2,c3,xb] at hc;omega
    simp only [characterAux,if_neg hn,ite_self]

theorem gasProduct_routing_commute (ctx : ApplyCtx) (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (routingAux interval fallback)=routingAux interval (gasProductAux ctx fallback) := by
  apply gasProduct_commute (routingAux interval)
  · intro a b p row col he
    simp only [routingAux,he]
  · intro a p row col hs hc
    have hn : col≠gBd := by simp only [ramt,c2,c3,xb] at hc;simp only [gBd];omega
    simp only [routingAux,routingActive,hs,sGP,sV,sRID,Nat.reduceBEq,Bool.false_and,Bool.false_or,Bool.false_eq_true,ite_false,if_neg hn]

theorem gasProduct_key_commute (ctx : ApplyCtx) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (keyAux accountId accessId fallback)=keyAux accountId accessId (gasProductAux ctx fallback) := by
  apply gasProduct_commute (keyAux accountId accessId)
  · intro a b p row col he
    simp only [keyAux,he]
  · intro a p row col hs hc
    apply keyAux_outside
    · simp only [ramt,c2,c3,xb] at hc
      simp only [keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK]
      omega
    · left;rw [hs];decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
