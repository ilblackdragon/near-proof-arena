import ZkFormal.NearV3.Assembly.RcptGasFlagPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem gasFlag_commute (F : (ReceiptPlan→Coord→Nat→Fp)→ReceiptPlan→Coord→Nat→Fp)
    (hlocal : ∀a b p row col,a p row col=b p row col→F a p row col=F b p row col)
    (hfree : ∀a p row col,row.state=sGP→(col=sumD ∨ col=invA)→F a p row col=a p row col)
    (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (F fallback)=F (gasFlagAux ctx fallback) := by
  funext p row col
  by_cases hs : row.state=sGP
  · by_cases hc : col=sumD ∨ col=invA
    · rw [hfree _ p row col hs hc]
      simp only [gasFlagAux,hfree fallback p row col hs hc]
    · have hn : col≠sumD ∧ col≠invA := by omega
      have he (a : ReceiptPlan→Coord→Nat→Fp) : gasFlagAux ctx a p row col=a p row col := by
        simp only [gasFlagAux,hn.1,hn.2,and_false,ite_false]
      rw [he]
      exact (hlocal _ _ p row col (he fallback)).symm
  · have he (a : ReceiptPlan→Coord→Nat→Fp) : gasFlagAux ctx a p row col=a p row col := by
      simp only [gasFlagAux,hs,false_and,ite_false]
    rw [he]
    exact (hlocal _ _ p row col (he fallback)).symm

theorem gasFlag_digest_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (digestMetadata fallback)=digestMetadata (gasFlagAux ctx fallback) := by
  apply gasFlag_commute digestMetadata
  · intro a b p row col he
    simp only [digestMetadata,he]
  · intro a p row col hs hc
    have hn : col≠gDg ∧ col≠dI ∧ col≠dL := by
      simp only [sumD,invA] at hc
      simp only [gDg,dI,dL]
      omega
    rcases hn with ⟨h0,h1,h2⟩
    simp only [digestMetadata,if_neg h0,if_neg h1,if_neg h2,ite_self]

theorem gasFlag_system_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (systemAux fallback)=systemAux (gasFlagAux ctx fallback) := by
  apply gasFlag_commute systemAux
  · intro a b p row col he
    simp only [systemAux,he]
  · intro a p row col hs hc
    have hn : col≠gV ∧ col≠gS ∧ col≠sx ∧ col≠invD ∧ col≠scnt ∧ col≠invL := by
      simp only [sumD,invA] at hc
      simp only [gV,gS,sx,invD,scnt,invL]
      omega
    rcases hn with ⟨h0,h1,h2,h3,h4,h5⟩
    simp only [systemAux,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,ite_self]

theorem gasFlag_length_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (characterLengthAux fallback)=characterLengthAux (gasFlagAux ctx fallback) := by
  apply gasFlag_commute characterLengthAux
  · intro a b p row col he
    simp only [characterLengthAux,he]
  · intro a p row col hs hc
    simp only [characterLengthAux,hs,List.mem_cons,List.not_mem_nil,or_false,sGP,sP,sV,sS,Nat.reduceEqDiff,false_or,ite_false]

theorem gasFlag_predecessor_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (predecessorAux fallback)=predecessorAux (gasFlagAux ctx fallback) := by
  apply gasFlag_commute predecessorAux
  · intro a b p row col he
    simp only [predecessorAux,he]
  · intro a p row col hs hc
    simp only [predecessorAux,hs,sGP,sP,Nat.reduceEqDiff,ite_false]

theorem gasFlag_named_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (namedAux fallback)=namedAux (gasFlagAux ctx fallback) := by
  apply gasFlag_commute namedAux
  · intro a b p row col he
    simp only [namedAux,he]
  · intro a p row col hs hc
    simp only [namedAux,hs,sGP,sV,Nat.reduceEqDiff,ite_false]

theorem gasFlag_character_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (characterAux fallback)=characterAux (gasFlagAux ctx fallback) := by
  apply gasFlag_commute characterAux
  · intro a b p row col he
    simp only [characterAux,he]
  · intro a p row col hs hc
    have hn : ¬(111≤col ∧ col≤123) := by simp only [sumD,invA] at hc;omega
    simp only [characterAux,if_neg hn,ite_self]

theorem gasFlag_routing_commute (ctx : ApplyCtx) (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (routingAux interval fallback)=routingAux interval (gasFlagAux ctx fallback) := by
  apply gasFlag_commute (routingAux interval)
  · intro a b p row col he
    simp only [routingAux,he]
  · intro a p row col hs hc
    have hn : col≠gBd := by simp only [sumD,invA] at hc;simp only [gBd];omega
    simp only [routingAux,routingActive,hs,sGP,sV,sRID,Nat.reduceBEq,Bool.false_and,Bool.false_or,Bool.false_eq_true,ite_false,if_neg hn]

theorem gasFlag_key_commute (ctx : ApplyCtx) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (keyAux accountId accessId fallback)=keyAux accountId accessId (gasFlagAux ctx fallback) := by
  apply gasFlag_commute (keyAux accountId accessId)
  · intro a b p row col he
    simp only [keyAux,he]
  · intro a p row col hs hc
    apply keyAux_outside
    · simp only [sumD,invA] at hc
      simp only [keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK]
      omega
    · left;rw [hs];decide

theorem gasFlag_borrow_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (gasBorrowAux ctx fallback)=gasBorrowAux ctx (gasFlagAux ctx fallback) :=
  (gasBorrow_flag_commute ctx fallback).symm

theorem gasFlag_effective_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (gasEffectiveAux ctx fallback)=gasEffectiveAux ctx (gasFlagAux ctx fallback) := by
  apply gasFlag_commute (gasEffectiveAux ctx)
  · intro a b p row col he
    simp only [gasEffectiveAux,he]
  · intro a p row col hs hc
    have hn : col≠pc := by simp only [sumD,invA] at hc;simp only [pc];omega
    simp only [gasEffectiveAux,hn,and_false,ite_false]

theorem gasFlag_delay_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (gasDelayAux ctx fallback)=gasDelayAux ctx (gasFlagAux ctx fallback) := by
  apply gasFlag_commute (gasDelayAux ctx)
  · intro a b p row col he
    simp only [gasDelayAux,he]
  · intro a p row col hs hc
    have hn : ¬(dl 0≤col ∧ col<dl 8) := by simp only [sumD,invA] at hc;simp only [dl];omega
    simp only [gasDelayAux,hs,hn,true_and,ite_false]

theorem gasEffective_constants_system (ctx : ApplyCtx) (fallback : ReceiptPlan→Nat→Fp) :
    gasEffectiveConstants ctx (systemConstants fallback)=systemConstants (gasEffectiveConstants ctx fallback) := by
  funext p col
  by_cases hc : col=gq
  · subst col;rfl
  · simp only [gasEffectiveConstants,systemConstants,if_neg hc]

theorem gasEffective_constants_price (ctx : ApplyCtx) (fallback : ReceiptPlan→Nat→Fp) :
    gasEffectiveConstants ctx (nativePriceConstants ctx fallback)=nativePriceConstants ctx (gasEffectiveConstants ctx fallback) := by
  funext p col
  by_cases hc : col=gq
  · subst col;rfl
  · simp only [gasEffectiveConstants,nativePriceConstants,if_neg hc]

end ZkFormal.NearV3.Assembly.RcptSkeleton
