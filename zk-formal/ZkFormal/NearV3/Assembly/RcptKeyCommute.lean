import ZkFormal.NearV3.Assembly.RcptKeyComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

def keySupport (row : Coord) (col : Nat) : Prop :=
  col∈keyColumns ∨ (row.state=sPK ∧ xb 0≤col ∧ col<xb 8)

theorem key_commute (F : (ReceiptPlan→Coord→Nat→Fp)→ReceiptPlan→Coord→Nat→Fp)
    (hlocal : ∀a b p row col,a p row col=b p row col→F a p row col=F b p row col)
    (hfree : ∀a p row col,keySupport row col→F a p row col=a p row col)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    keyAux accountId accessId (F fallback)=F (keyAux accountId accessId fallback) := by
  funext p row col
  by_cases hc : keySupport row col
  · rw [hfree _ p row col hc]
    simp only [keyAux,hfree fallback p row col hc]
  · have hm : col∉keyColumns := fun hh=>hc (Or.inl hh)
    have hb : row.state≠sPK ∨ col<xb 0 ∨ xb 8≤col := by
      simp only [keySupport] at hc
      omega
    rw [keyAux_outside accountId accessId _ p row col hm hb]
    exact (hlocal _ _ p row col (keyAux_outside accountId accessId fallback p row col hm hb)).symm

theorem key_digest_commute (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    keyAux accountId accessId (digestMetadata fallback)=digestMetadata (keyAux accountId accessId fallback) := by
  apply key_commute digestMetadata
  · intro a b p row col he
    simp only [digestMetadata,he]
  · intro a p row col hc
    have hn : col≠gDg ∧ col≠dI ∧ col≠dL := by
      simp only [keySupport,keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK,xb] at hc
      simp only [gDg,dI,dL]
      omega
    rcases hn with ⟨h0,h1,h2⟩
    simp only [digestMetadata,if_neg h0,if_neg h1,if_neg h2,ite_self]

theorem key_predecessor_commute (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    keyAux accountId accessId (predecessorAux fallback)=predecessorAux (keyAux accountId accessId fallback) := by
  apply key_commute predecessorAux
  · intro a b p row col he
    simp only [predecessorAux,he]
  · intro a p row col hc
    have hn : col≠acc ∧ col≠p1 ∧ col≠isys := by
      simp only [keySupport,keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK,xb] at hc
      simp only [acc,p1,isys]
      omega
    rcases hn with ⟨h0,h1,h2⟩
    simp only [predecessorAux,if_neg h0,if_neg h1,if_neg h2,ite_self]

theorem key_named_commute (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    keyAux accountId accessId (namedAux fallback)=namedAux (keyAux accountId accessId fallback) := by
  apply key_commute namedAux
  · intro a b p row col he
    simp only [namedAux,he]
  · intro a p row col hc
    have hn : col≠acc ∧ col≠vc0 ∧ col≠vc1 ∧ col≠h01 ∧ col≠p1 ∧ col≠p2 ∧ col≠p3 ∧ col≠i1 ∧ col≠i2 ∧ col≠i3 := by
      simp only [keySupport,keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK,xb] at hc
      simp only [acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
      omega
    rcases hn with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    simp only [namedAux,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,ite_self]

theorem key_system_commute (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    keyAux accountId accessId (systemAux fallback)=systemAux (keyAux accountId accessId fallback) := by
  apply key_commute systemAux
  · intro a b p row col he
    simp only [systemAux,he]
  · intro a p row col hc
    have hn : col≠gV ∧ col≠gS ∧ col≠sx ∧ col≠invD ∧ col≠scnt ∧ col≠invL := by
      simp only [keySupport,keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK,xb] at hc
      simp only [gV,gS,sx,invD,scnt,invL]
      omega
    rcases hn with ⟨h0,h1,h2,h3,h4,h5⟩
    simp only [systemAux,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5]

theorem key_length_commute (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    keyAux accountId accessId (characterLengthAux fallback)=characterLengthAux (keyAux accountId accessId fallback) := by
  apply key_commute characterLengthAux
  · intro a b p row col he
    simp only [characterLengthAux,he]
  · intro a p row col hc
    rcases hc with hc|⟨hs,hlo,hhi⟩
    · have hn : ¬(xb 0≤col ∧ col<xb 6) ∧ ¬(xb 6≤col ∧ col<xb 12) := by
        simp only [keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK] at hc
        simp only [xb]
        omega
      simp only [characterLengthAux,if_neg hn.1,if_neg hn.2,ite_self]
    · have hn : row.state∉[sP,sV,sS] := by rw [hs];decide
      simp only [characterLengthAux,if_neg hn]

theorem key_routing_commute (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (interval : ReceiptPlan→Option Bytes×Option Bytes) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    keyAux accountId accessId (routingAux interval fallback)=routingAux interval (keyAux accountId accessId fallback) := by
  apply key_commute (routingAux interval)
  · intro a b p row col he
    simp only [routingAux,he]
  · intro a p row col hc
    have hn : routingScratch col=false ∧ col≠gBd := by
      constructor
      · apply Bool.eq_false_iff.mpr
        intro ht
        have hb := routingScratch_bounds col ht
        simp only [keySupport,keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK,xb] at hc
        omega
      · simp only [keySupport,keyColumns,List.mem_cons,List.not_mem_nil,or_false,tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK,xb] at hc
        simp only [gBd]
        omega
    simp only [routingAux,hn.1,Bool.and_false,Bool.false_eq_true,ite_false,if_neg hn.2]

end ZkFormal.NearV3.Assembly.RcptSkeleton
