import ZkFormal.NearV3.Assembly.RcptDepositFrameCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def depositFinalAux (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) : ReceiptPlan→Coord→Nat→Fp :=
  depositAgeAux previous (depositAux accounts fallback)

theorem depositFinalAux_outside (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (a : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (h : ¬depositOwned row col) : depositFinalAux previous accounts a p row col=a p row col := by
  have h1 : ¬(row.state=sDEP ∧ col=r1) := by intro hh;exact h (Or.inl hh.2)
  have h2 : ¬(row.state=sDEP ∧ row.index=0 ∧ xb 53≤col ∧ col<xb 66) := by
    intro hh
    apply h
    right;right;refine ⟨hh.1,?_⟩
    simp only [r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at *
    omega
  simp only [depositFinalAux,depositAgeAux,if_neg h1,if_neg h2]
  exact depositAux_outside accounts a p row col h

theorem depositFinalAux_owned (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (a b : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (h : depositOwned row col) : depositFinalAux previous accounts a p row col=depositFinalAux previous accounts b p row col := by
  simp only [depositFinalAux,depositAgeAux,depositAux_owned accounts a b p row col h]

theorem depositFinalAux_commute
    (F : (ReceiptPlan→Coord→Nat→Fp)→ReceiptPlan→Coord→Nat→Fp)
    (hlocal : ∀a b p row col,a p row col=b p row col→F a p row col=F b p row col)
    (hfree : ∀a p row col,depositOwned row col→F a p row col=a p row col)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositFinalAux previous accounts (F fallback)=F (depositFinalAux previous accounts fallback) := by
  funext p row col
  by_cases h : depositOwned row col
  · rw [hfree _ p row col h]
    exact depositFinalAux_owned previous accounts _ _ p row col h
  · rw [depositFinalAux_outside previous accounts _ p row col h]
    exact (hlocal _ _ p row col (depositFinalAux_outside previous accounts fallback p row col h)).symm

theorem depositFinal_product_commute (ctx : ApplyCtx) (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (depositFinalAux previous accounts fallback)=depositFinalAux previous accounts (gasProductAux ctx fallback) := by
  apply gasProduct_commute (depositFinalAux previous accounts)
  · intro a b p row col he
    simp only [depositFinalAux,depositAgeAux,depositAux,he]
  · intro a p row col hs hc
    apply depositFinalAux_outside
    simp only [depositOwned,hs,sGP,sDEP,Nat.reduceEqDiff,false_and,or_false]
    simp only [ramt,c2,c3,xb] at hc
    simp only [r1,st]
    omega

theorem depositFinal_token_commute (tokens : ReceiptPlan→TokenInput) (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (depositFinalAux previous accounts fallback)=depositFinalAux previous accounts (gasTokenAux tokens fallback) := by
  apply gasToken_commute (depositFinalAux previous accounts)
  · intro a b p row col he
    simp only [depositFinalAux,depositAgeAux,depositAux,he]
  · intro a p row col hs hc
    apply depositFinalAux_outside
    simp only [depositOwned,hs,sGP,sDEP,Nat.reduceEqDiff,false_and,or_false]
    simp only [burnt,c4,xb] at hc
    simp only [r1,st]
    omega

theorem depositFinal_flag_commute (ctx : ApplyCtx) (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (depositFinalAux previous accounts fallback)=depositFinalAux previous accounts (gasFlagAux ctx fallback) := by
  apply gasFlag_commute (depositFinalAux previous accounts)
  · intro a b p row col he
    simp only [depositFinalAux,depositAgeAux,depositAux,he]
  · intro a p row col hs hc
    apply depositFinalAux_outside
    simp only [depositOwned,hs,sGP,sDEP,Nat.reduceEqDiff,false_and,or_false]
    simp only [sumD,invA] at hc
    simp only [r1,st]
    omega

theorem depositFinal_delay_commute (ctx : ApplyCtx) (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    candidateGasDelayAux ctx (depositFinalAux previous accounts fallback)=depositFinalAux previous accounts (candidateGasDelayAux ctx fallback) := by
  apply candidateGasDelay_commute (depositFinalAux previous accounts)
  · intro a b p row col he
    simp only [depositFinalAux,depositAgeAux,depositAux,he]
  · intro a p row col hs hc
    apply depositFinalAux_outside
    simp only [depositOwned,hs,sGP,sDEP,Nat.reduceEqDiff,false_and,or_false]
    simp only [dl] at hc
    simp only [r1,st]
    omega

theorem depositFinal_digest_commute (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositFinalAux previous accounts (digestMetadata fallback)=digestMetadata (depositFinalAux previous accounts fallback) := by
  apply depositFinalAux_commute digestMetadata
  · intro a b p row col he
    simp only [digestMetadata,he]
  · intro a p row col hc
    have hn : col≠gDg ∧ col≠dI ∧ col≠dL := by
      simp only [depositOwned,r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at hc
      simp only [gDg,dI,dL]
      omega
    rcases hn with ⟨h0,h1,h2⟩
    simp only [digestMetadata,if_neg h0,if_neg h1,if_neg h2,ite_self]

theorem depositFinal_system_commute (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositFinalAux previous accounts (systemAux fallback)=systemAux (depositFinalAux previous accounts fallback) := by
  apply depositFinalAux_commute systemAux
  · intro a b p row col he
    simp only [systemAux,he]
  · intro a p row col hc
    have hn : col≠gV ∧ col≠gS ∧ col≠sx ∧ col≠invD ∧ col≠scnt ∧ col≠invL := by
      simp only [depositOwned,r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at hc
      simp only [gV,gS,sx,invD,scnt,invL]
      omega
    rcases hn with ⟨h0,h1,h2,h3,h4,h5⟩
    simp only [systemAux,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,ite_self]

theorem depositFinal_length_commute (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositFinalAux previous accounts (characterLengthAux fallback)=characterLengthAux (depositFinalAux previous accounts fallback) := by
  apply depositFinalAux_commute characterLengthAux
  · intro a b p row col he
    simp only [characterLengthAux,he]
  · intro a p row col hc
    rcases hc with rfl|rfl|⟨hs,_⟩
    · simp [characterLengthAux,r1,dl,xb]
    · simp [characterLengthAux,st,dl,xb]
    · simp only [characterLengthAux,hs,List.mem_cons,List.not_mem_nil,or_false,sDEP,sP,sV,sS,Nat.reduceEqDiff,false_or,ite_false]

theorem depositFinal_predecessor_commute (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositFinalAux previous accounts (predecessorAux fallback)=predecessorAux (depositFinalAux previous accounts fallback) := by
  apply depositFinalAux_commute predecessorAux
  · intro a b p row col he
    simp only [predecessorAux,he]
  · intro a p row col hc
    rcases hc with rfl|rfl|⟨hs,_⟩
    · simp [predecessorAux,r1,acc,p1,isys]
    · simp [predecessorAux,st,acc,p1,isys]
    · simp only [predecessorAux,hs,List.mem_cons,List.not_mem_nil,or_false,sDEP,sP,sV,sS,Nat.reduceEqDiff,false_or,ite_false]

theorem depositFinal_named_commute (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositFinalAux previous accounts (namedAux fallback)=namedAux (depositFinalAux previous accounts fallback) := by
  apply depositFinalAux_commute namedAux
  · intro a b p row col he
    simp only [namedAux,he]
  · intro a p row col hc
    rcases hc with rfl|rfl|⟨hs,_⟩
    · simp [namedAux,r1,acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
    · simp [namedAux,st,acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
    · simp only [namedAux,hs,List.mem_cons,List.not_mem_nil,or_false,sDEP,sP,sV,sS,Nat.reduceEqDiff,false_or,ite_false]

theorem depositFinal_character_commute (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositFinalAux previous accounts (characterAux fallback)=characterAux (depositFinalAux previous accounts fallback) := by
  apply depositFinalAux_commute characterAux
  · intro a b p row col he;simp only [characterAux,he]
  · intro a p row col hc
    have hn : ¬(111≤col ∧ col≤123) := by
      simp only [depositOwned,r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at hc
      omega
    simp only [characterAux,if_neg hn,ite_self]

theorem depositFinal_key_commute (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositFinalAux previous accounts (keyAux accountId accessId fallback)=keyAux accountId accessId (depositFinalAux previous accounts fallback) := by
  apply depositFinalAux_commute (keyAux accountId accessId)
  · intro a b p row col he;simp only [keyAux,he]
  · intro a p row col hc
    apply keyAux_outside
    · simp only [depositOwned,r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at hc
      simp only [keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK]
      omega
    · rcases hc with rfl|rfl|⟨hs,_⟩
      · right;left;decide
      · right;right;decide
      · left;rw [hs];decide

theorem depositFinal_routing_commute (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositFinalAux previous accounts (routingAux interval fallback)=routingAux interval (depositFinalAux previous accounts fallback) := by
  apply depositFinalAux_commute (routingAux interval)
  · intro a b p row col he;simp only [routingAux,he]
  · intro a p row col hc
    have hn : col≠gBd := by
      simp only [depositOwned,r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at hc
      simp only [gBd];omega
    rcases hc with rfl|rfl|⟨hs,_⟩
    · have hh : routingScratch r1=false := by decide
      simp only [routingAux,hh,Bool.and_false,Bool.false_eq_true,ite_false,if_neg hn]
    · have hh : routingScratch st=false := by decide
      simp only [routingAux,hh,Bool.and_false,Bool.false_eq_true,ite_false,if_neg hn]
    · simp only [routingAux,routingActive,hs,sDEP,sV,sRID,Nat.reduceBEq,Bool.false_and,Bool.false_or,Bool.false_eq_true,ite_false,if_neg hn]

theorem depositFinal_borrow_commute (ctx : ApplyCtx) (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasBorrowAux ctx (depositFinalAux previous accounts fallback)=depositFinalAux previous accounts (gasBorrowAux ctx fallback) := by
  apply gasBorrow_commute (depositFinalAux previous accounts)
  · intro a b p row col he;simp only [depositFinalAux,depositAgeAux,depositAux,he]
  · intro a p row col hs hc
    apply depositFinalAux_outside
    simp only [depositOwned,hs,sGP,sDEP,Nat.reduceEqDiff,false_and,or_false]
    simp only [c1,xb] at hc
    simp only [r1,st];omega

theorem depositFinal_effective_commute (ctx : ApplyCtx) (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (depositFinalAux previous accounts fallback)=depositFinalAux previous accounts (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (depositFinalAux previous accounts)
  · intro a b p row col he;simp only [depositFinalAux,depositAgeAux,depositAux,he]
  · intro a p row hs
    apply depositFinalAux_outside
    simp only [depositOwned,hs,sGP,sDEP,Nat.reduceEqDiff,false_and,or_false]
    decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
