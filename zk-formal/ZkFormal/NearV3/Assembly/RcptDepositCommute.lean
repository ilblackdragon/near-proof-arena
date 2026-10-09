import ZkFormal.NearV3.Assembly.RcptDepositNativePhysical
import ZkFormal.NearV3.Assembly.RcptGasCandidateCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Exact scratch ownership, including the two globally zeroed columns. -/
def depositOwned (row : Coord) (col : Nat) : Prop :=
  col=r1 ∨ col=st ∨ (row.state=sDEP ∧
    (col=bef ∨ col=lk ∨ col=c1 ∨ col=c2 ∨ col=c3 ∨ col=c4 ∨
     col=dsum ∨ col=invB ∨ (dl 0≤col ∧ col<dl 7) ∨ (xb 0≤col ∧ col<xb 66)))

theorem depositAux_outside (accounts : ReceiptPlan→Account)
    (a : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (h : ¬depositOwned row col) : depositAux accounts a p row col=a p row col := by
  simp only [depositOwned,not_or,not_and] at h
  rcases h with ⟨hr,ht,hrest⟩
  by_cases hs : row.state=sDEP
  · have hc := hrest hs
    have hd : ¬(dl 0≤col ∧ col<dl 7) := by omega
    have hx : ¬(xb 0≤col ∧ col<xb 66) := by omega
    simp only [depositAux,hr,ht,hs,ite_true,ite_false,hc.1,hc.2.1,hc.2.2.1,
      hc.2.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2.1,hc.2.2.2.2.2.2.1,
      hc.2.2.2.2.2.2.2.1,hd,hx]
  · simp only [depositAux,hr,ht,hs,ite_false]

theorem depositAux_owned (accounts : ReceiptPlan→Account)
    (a b : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (h : depositOwned row col) : depositAux accounts a p row col=depositAux accounts b p row col := by
  rcases h with hr|ht|⟨hs,hc⟩
  · simp only [depositAux,hr,ite_true]
  · simp only [depositAux,ht,ite_true]
  · rcases hc with hc|hc|hc|hc|hc|hc|hc|hc|hc|hc <;>
      simp only [depositAux,hs,hc,and_self,ite_true]

theorem depositAux_commute
    (F : (ReceiptPlan→Coord→Nat→Fp)→ReceiptPlan→Coord→Nat→Fp)
    (hlocal : ∀a b p row col,a p row col=b p row col→F a p row col=F b p row col)
    (hfree : ∀a p row col,depositOwned row col→F a p row col=a p row col)
    (accounts : ReceiptPlan→Account) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositAux accounts (F fallback)=F (depositAux accounts fallback) := by
  funext p row col
  by_cases h : depositOwned row col
  · rw [hfree _ p row col h]
    exact depositAux_owned accounts _ _ p row col h
  · rw [depositAux_outside accounts _ p row col h]
    exact (hlocal _ _ p row col (depositAux_outside accounts fallback p row col h)).symm

theorem deposit_product_commute (ctx : ApplyCtx) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasProductAux ctx (depositAux accounts fallback)=depositAux accounts (gasProductAux ctx fallback) := by
  apply gasProduct_commute (depositAux accounts)
  · intro a b p row col he
    simp only [depositAux,he]
  · intro a p row col hs hc
    apply depositAux_outside
    simp only [depositOwned,hs,sGP,sDEP,Nat.reduceEqDiff,false_and,or_false]
    simp only [ramt,c2,c3,xb] at hc
    simp only [r1,st]
    omega

theorem deposit_token_commute (tokens : ReceiptPlan→TokenInput) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasTokenAux tokens (depositAux accounts fallback)=depositAux accounts (gasTokenAux tokens fallback) := by
  apply gasToken_commute (depositAux accounts)
  · intro a b p row col he
    simp only [depositAux,he]
  · intro a p row col hs hc
    apply depositAux_outside
    simp only [depositOwned,hs,sGP,sDEP,Nat.reduceEqDiff,false_and,or_false]
    simp only [burnt,c4,xb] at hc
    simp only [r1,st]
    omega

theorem deposit_flag_commute (ctx : ApplyCtx) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasFlagAux ctx (depositAux accounts fallback)=depositAux accounts (gasFlagAux ctx fallback) := by
  apply gasFlag_commute (depositAux accounts)
  · intro a b p row col he
    simp only [depositAux,he]
  · intro a p row col hs hc
    apply depositAux_outside
    simp only [depositOwned,hs,sGP,sDEP,Nat.reduceEqDiff,false_and,or_false]
    simp only [sumD,invA] at hc
    simp only [r1,st]
    omega

theorem deposit_delay_commute (ctx : ApplyCtx) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    candidateGasDelayAux ctx (depositAux accounts fallback)=depositAux accounts (candidateGasDelayAux ctx fallback) := by
  apply candidateGasDelay_commute (depositAux accounts)
  · intro a b p row col he
    simp only [depositAux,he]
  · intro a p row col hs hc
    apply depositAux_outside
    simp only [depositOwned,hs,sGP,sDEP,Nat.reduceEqDiff,false_and,or_false]
    simp only [dl] at hc
    simp only [r1,st]
    omega

theorem deposit_digest_commute (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositAux accounts (digestMetadata fallback)=digestMetadata (depositAux accounts fallback) := by
  apply depositAux_commute digestMetadata
  · intro a b p row col he
    simp only [digestMetadata,he]
  · intro a p row col hc
    have hn : col≠gDg ∧ col≠dI ∧ col≠dL := by
      simp only [depositOwned,r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at hc
      simp only [gDg,dI,dL]
      omega
    rcases hn with ⟨h0,h1,h2⟩
    simp only [digestMetadata,if_neg h0,if_neg h1,if_neg h2,ite_self]

theorem deposit_system_commute (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositAux accounts (systemAux fallback)=systemAux (depositAux accounts fallback) := by
  apply depositAux_commute systemAux
  · intro a b p row col he
    simp only [systemAux,he]
  · intro a p row col hc
    have hn : col≠gV ∧ col≠gS ∧ col≠sx ∧ col≠invD ∧ col≠scnt ∧ col≠invL := by
      simp only [depositOwned,r1,st,bef,lk,c1,c2,c3,c4,dsum,invB,dl,xb] at hc
      simp only [gV,gS,sx,invD,scnt,invL]
      omega
    rcases hn with ⟨h0,h1,h2,h3,h4,h5⟩
    simp only [systemAux,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,ite_self]

theorem deposit_length_commute (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositAux accounts (characterLengthAux fallback)=characterLengthAux (depositAux accounts fallback) := by
  apply depositAux_commute characterLengthAux
  · intro a b p row col he
    simp only [characterLengthAux,he]
  · intro a p row col hc
    rcases hc with rfl|rfl|⟨hs,_⟩
    · simp [characterLengthAux,r1,dl,xb]
    · simp [characterLengthAux,st,dl,xb]
    · simp only [characterLengthAux,hs,List.mem_cons,List.not_mem_nil,or_false,sDEP,sP,sV,sS,Nat.reduceEqDiff,false_or,ite_false]

theorem deposit_predecessor_commute (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositAux accounts (predecessorAux fallback)=predecessorAux (depositAux accounts fallback) := by
  apply depositAux_commute predecessorAux
  · intro a b p row col he
    simp only [predecessorAux,he]
  · intro a p row col hc
    rcases hc with rfl|rfl|⟨hs,_⟩
    · simp [predecessorAux,r1,acc,p1,isys]
    · simp [predecessorAux,st,acc,p1,isys]
    · simp only [predecessorAux,hs,List.mem_cons,List.not_mem_nil,or_false,sDEP,sP,sV,sS,Nat.reduceEqDiff,false_or,ite_false]

theorem deposit_named_commute (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    depositAux accounts (namedAux fallback)=namedAux (depositAux accounts fallback) := by
  apply depositAux_commute namedAux
  · intro a b p row col he
    simp only [namedAux,he]
  · intro a p row col hc
    rcases hc with rfl|rfl|⟨hs,_⟩
    · simp [namedAux,r1,acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
    · simp [namedAux,st,acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
    · simp only [namedAux,hs,List.mem_cons,List.not_mem_nil,or_false,sDEP,sP,sV,sS,Nat.reduceEqDiff,false_or,ite_false]

end ZkFormal.NearV3.Assembly.RcptSkeleton
