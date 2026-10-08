import ZkFormal.NearV3.Assembly.RcptGasTokenPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem gasToken_commute (F : (ReceiptPlan→Coord→Nat→Fp)→ReceiptPlan→Coord→Nat→Fp)
    (hlocal : ∀a b p row col,a p row col=b p row col→F a p row col=F b p row col)
    (hfree : ∀a p row col,row.state=sGP→(col=burnt ∨ col=c4 ∨ col=xb 39)→F a p row col=a p row col)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (F fallback)=F (gasTokenAux tokens fallback) := by
  funext p row col
  by_cases hs : row.state=sGP
  · by_cases hc : col=burnt ∨ col=c4 ∨ col=xb 39
    · rw [hfree _ p row col hs hc]
      simp only [gasTokenAux,hfree fallback p row col hs hc]
    · have hn : col≠burnt ∧ col≠c4 ∧ col≠xb 39 := by omega
      have he (a : ReceiptPlan→Coord→Nat→Fp) : gasTokenAux tokens a p row col=a p row col := by
        simp only [gasTokenAux,hn.1,hn.2.1,hn.2.2,and_false,ite_false]
      rw [he]
      exact (hlocal _ _ p row col (he fallback)).symm
  · have he (a : ReceiptPlan→Coord→Nat→Fp) : gasTokenAux tokens a p row col=a p row col := by
      simp only [gasTokenAux,hs,false_and,ite_false]
    rw [he]
    exact (hlocal _ _ p row col (he fallback)).symm

theorem gasToken_digest_commute (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (digestMetadata fallback)=digestMetadata (gasTokenAux tokens fallback) := by
  apply gasToken_commute digestMetadata
  · intro a b p row col he
    simp only [digestMetadata,he]
  · intro a p row col hs hc
    have hn : col≠gDg ∧ col≠dI ∧ col≠dL := by
      simp only [burnt,c4,xb] at hc
      simp only [gDg,dI,dL]
      omega
    rcases hn with ⟨h0,h1,h2⟩
    simp only [digestMetadata,if_neg h0,if_neg h1,if_neg h2,ite_self]

theorem gasToken_system_commute (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (systemAux fallback)=systemAux (gasTokenAux tokens fallback) := by
  apply gasToken_commute systemAux
  · intro a b p row col he
    simp only [systemAux,he]
  · intro a p row col hs hc
    have hn : col≠gV ∧ col≠gS ∧ col≠sx ∧ col≠invD ∧ col≠scnt ∧ col≠invL := by
      simp only [burnt,c4,xb] at hc
      simp only [gV,gS,sx,invD,scnt,invL]
      omega
    rcases hn with ⟨h0,h1,h2,h3,h4,h5⟩
    simp only [systemAux,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,ite_self]

theorem gasToken_length_commute (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (characterLengthAux fallback)=characterLengthAux (gasTokenAux tokens fallback) := by
  apply gasToken_commute characterLengthAux
  · intro a b p row col he
    simp only [characterLengthAux,he]
  · intro a p row col hs hc
    simp only [characterLengthAux,hs,List.mem_cons,List.not_mem_nil,or_false,sGP,sP,sV,sS,Nat.reduceEqDiff,false_or,ite_false]

theorem gasToken_predecessor_commute (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (predecessorAux fallback)=predecessorAux (gasTokenAux tokens fallback) := by
  apply gasToken_commute predecessorAux
  · intro a b p row col he
    simp only [predecessorAux,he]
  · intro a p row col hs hc
    simp only [predecessorAux,hs,sGP,sP,Nat.reduceEqDiff,ite_false]

theorem gasToken_named_commute (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (namedAux fallback)=namedAux (gasTokenAux tokens fallback) := by
  apply gasToken_commute namedAux
  · intro a b p row col he
    simp only [namedAux,he]
  · intro a p row col hs hc
    simp only [namedAux,hs,sGP,sV,Nat.reduceEqDiff,ite_false]

theorem gasToken_character_commute (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (characterAux fallback)=characterAux (gasTokenAux tokens fallback) := by
  apply gasToken_commute characterAux
  · intro a b p row col he
    simp only [characterAux,he]
  · intro a p row col hs hc
    have hn : ¬(111≤col ∧ col≤123) := by simp only [burnt,c4,xb] at hc;omega
    simp only [characterAux,if_neg hn,ite_self]

theorem gasToken_routing_commute (tokens : ReceiptPlan→TokenInput) (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (routingAux interval fallback)=routingAux interval (gasTokenAux tokens fallback) := by
  apply gasToken_commute (routingAux interval)
  · intro a b p row col he
    simp only [routingAux,he]
  · intro a p row col hs hc
    have hn : col≠gBd := by simp only [burnt,c4,xb] at hc;simp only [gBd];omega
    simp only [routingAux,routingActive,hs,sGP,sV,sRID,Nat.reduceBEq,Bool.false_and,Bool.false_or,Bool.false_eq_true,ite_false,if_neg hn]

theorem gasToken_key_commute (tokens : ReceiptPlan→TokenInput) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (keyAux accountId accessId fallback)=keyAux accountId accessId (gasTokenAux tokens fallback) := by
  apply gasToken_commute (keyAux accountId accessId)
  · intro a b p row col he
    simp only [keyAux,he]
  · intro a p row col hs hc
    apply keyAux_outside
    · simp only [burnt,c4,xb] at hc
      simp only [keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK]
      omega
    · left;rw [hs];decide

theorem gasToken_borrow_commute (tokens : ReceiptPlan→TokenInput) (ctx : ApplyCtx)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (gasBorrowAux ctx fallback)=gasBorrowAux ctx (gasTokenAux tokens fallback) := by
  apply gasToken_commute (gasBorrowAux ctx)
  · intro a b p row col he
    simp only [gasBorrowAux,he]
  · intro a p row col hs hc
    have hn : col≠c1 ∧ ¬(xb 0≤col ∧ col<xb 8) ∧ col≠xb 8 := by
      simp only [burnt,c4,xb] at hc
      simp only [c1,xb]
      omega
    simp only [gasBorrowAux,hs,ite_true,hn.1,hn.2.1,hn.2.2,ite_false]

theorem gasToken_effective_commute (tokens : ReceiptPlan→TokenInput) (ctx : ApplyCtx)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (gasEffectiveAux ctx fallback)=gasEffectiveAux ctx (gasTokenAux tokens fallback) := by
  apply gasToken_commute (gasEffectiveAux ctx)
  · intro a b p row col he
    simp only [gasEffectiveAux,he]
  · intro a p row col hs hc
    have hn : col≠pc := by simp only [burnt,c4,xb] at hc;simp only [pc];omega
    simp only [gasEffectiveAux,hn,and_false,ite_false]

theorem gasToken_delay_commute (tokens : ReceiptPlan→TokenInput) (ctx : ApplyCtx)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (gasDelayAux ctx fallback)=gasDelayAux ctx (gasTokenAux tokens fallback) := by
  apply gasToken_commute (gasDelayAux ctx)
  · intro a b p row col he
    simp only [gasDelayAux,he]
  · intro a p row col hs hc
    have hn : ¬(dl 0≤col ∧ col<dl 8) := by simp only [burnt,c4,xb] at hc;simp only [dl];omega
    simp only [gasDelayAux,hs,hn,true_and,ite_false]

theorem gasToken_flag_commute (tokens : ReceiptPlan→TokenInput) (ctx : ApplyCtx)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (gasFlagAux ctx fallback)=gasFlagAux ctx (gasTokenAux tokens fallback) := by
  apply gasToken_commute (gasFlagAux ctx)
  · intro a b p row col he
    simp only [gasFlagAux,he]
  · intro a p row col hs hc
    have hn : col≠sumD ∧ col≠invA := by simp only [burnt,c4,xb] at hc;simp only [sumD,invA];omega
    simp only [gasFlagAux,hn.1,hn.2,and_false,ite_false]

end ZkFormal.NearV3.Assembly.RcptSkeleton
