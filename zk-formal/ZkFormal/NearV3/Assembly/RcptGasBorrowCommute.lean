import ZkFormal.NearV3.Assembly.RcptGasBorrowTransition

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem gasBorrow_commute (F : (ReceiptPlan→Coord→Nat→Fp)→ReceiptPlan→Coord→Nat→Fp)
    (hlocal : ∀a b p row col,a p row col=b p row col→F a p row col=F b p row col)
    (hfree : ∀a p row col,row.state=sGP→(col=c1 ∨ (xb 0≤col ∧ col<xb 9))→F a p row col=a p row col)
    (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (F fallback)=F (gasBorrowAux ctx fallback) := by
  funext p row col
  by_cases hs : row.state=sGP
  · by_cases hc : col=c1 ∨ (xb 0≤col ∧ col<xb 9)
    · rw [hfree _ p row col hs hc]
      simp only [gasBorrowAux,hfree fallback p row col hs hc]
    · have hn : col≠c1 ∧ ¬(xb 0≤col ∧ col<xb 8) ∧ col≠xb 8 := by simp only [xb] at *;omega
      have he (a : ReceiptPlan→Coord→Nat→Fp) : gasBorrowAux ctx a p row col=a p row col := by
        simp only [gasBorrowAux,if_pos hs,if_neg hn.1,if_neg hn.2.1,if_neg hn.2.2]
      rw [he]
      exact (hlocal _ _ p row col (he fallback)).symm
  · have he (a : ReceiptPlan→Coord→Nat→Fp) : gasBorrowAux ctx a p row col=a p row col := by simp only [gasBorrowAux,if_neg hs]
    rw [he]
    exact (hlocal _ _ p row col (he fallback)).symm

theorem gasBorrow_digest_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (digestMetadata fallback)=digestMetadata (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute digestMetadata
  · intro a b p row col he
    simp only [digestMetadata,he]
  · intro a p row col hs hc
    have hn : col≠gDg ∧ col≠dI ∧ col≠dL := by
      simp only [c1,xb] at hc
      simp only [gDg,dI,dL]
      omega
    rcases hn with ⟨h0,h1,h2⟩
    simp only [digestMetadata,if_neg h0,if_neg h1,if_neg h2,ite_self]

theorem gasBorrow_system_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (systemAux fallback)=systemAux (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute systemAux
  · intro a b p row col he
    simp only [systemAux,he]
  · intro a p row col hs hc
    have hn : col≠gV ∧ col≠gS ∧ col≠sx ∧ col≠invD ∧ col≠scnt ∧ col≠invL := by
      simp only [c1,xb] at hc
      simp only [gV,gS,sx,invD,scnt,invL]
      omega
    rcases hn with ⟨h0,h1,h2,h3,h4,h5⟩
    simp only [systemAux,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,ite_self]

theorem gasBorrow_length_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (characterLengthAux fallback)=characterLengthAux (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute characterLengthAux
  · intro a b p row col he
    simp only [characterLengthAux,he]
  · intro a p row col hs hc
    simp only [characterLengthAux,hs,List.mem_cons,List.not_mem_nil,or_false,sGP,sP,sV,sS,Nat.reduceEqDiff,false_or,ite_false]

theorem gasBorrow_predecessor_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (predecessorAux fallback)=predecessorAux (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute predecessorAux
  · intro a b p row col he
    simp only [predecessorAux,he]
  · intro a p row col hs hc
    simp only [predecessorAux,hs,sGP,sP,Nat.reduceEqDiff,ite_false]

theorem gasBorrow_named_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (namedAux fallback)=namedAux (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute namedAux
  · intro a b p row col he
    simp only [namedAux,he]
  · intro a p row col hs hc
    simp only [namedAux,hs,sGP,sV,Nat.reduceEqDiff,ite_false]

theorem gasBorrow_character_commute (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (characterAux fallback)=characterAux (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute characterAux
  · intro a b p row col he
    simp only [characterAux,he]
  · intro a p row col hs hc
    have hn : ¬(111≤col ∧ col≤123) := by simp only [c1,xb] at hc;omega
    simp only [characterAux,if_neg hn,ite_self]

theorem gasBorrow_routing_commute (ctx : ApplyCtx) (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (routingAux interval fallback)=routingAux interval (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute (routingAux interval)
  · intro a b p row col he
    simp only [routingAux,he]
  · intro a p row col hs hc
    have hn : col≠gBd := by simp only [c1,xb] at hc;simp only [gBd];omega
    simp only [routingAux,routingActive,hs,sGP,sV,sRID,Nat.reduceBEq,Bool.false_and,Bool.false_or,Bool.false_eq_true,ite_false,if_neg hn]

theorem gasBorrow_key_commute (ctx : ApplyCtx) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (keyAux accountId accessId fallback)=keyAux accountId accessId (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute (keyAux accountId accessId)
  · intro a b p row col he
    simp only [keyAux,he]
  · intro a p row col hs hc
    apply keyAux_outside
    · simp only [c1,xb] at hc
      simp only [keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK]
      omega
    · left;rw [hs];decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
