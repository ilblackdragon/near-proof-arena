import ZkFormal.NearV3.Assembly.RcptRoutingPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem routing_commute (F : (ReceiptPlan→Coord→Nat→Fp)→ReceiptPlan→Coord→Nat→Fp)
    (hlocal : ∀a b p row col,a p row col=b p row col→F a p row col=F b p row col)
    (hfree : ∀a p row col,routingScratch col=true→F a p row col=a p row col)
    (interval : ReceiptPlan→Option Bytes×Option Bytes) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    routingAux interval (F fallback)=F (routingAux interval fallback) := by
  funext p row col
  by_cases hc : routingScratch col=true
  · rw [hfree _ p row col hc]
    simp only [routingAux,hfree fallback p row col hc]
  · have hz : routingScratch col=false := Bool.eq_false_iff.mpr hc
    have hg : col≠gBd := by intro he;subst col;exact hc (by decide)
    have he (a : ReceiptPlan→Coord→Nat→Fp) : routingAux interval a p row col=a p row col := by
      simp only [routingAux,hz,Bool.and_false,Bool.false_eq_true,ite_false,if_neg hg]
    rw [he]
    exact (hlocal _ _ p row col (he fallback)).symm

theorem routing_character_commute (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    routingAux interval (characterAux fallback)=characterAux (routingAux interval fallback) := by
  apply routing_commute characterAux
  · intro a b p row col he
    simp only [characterAux,he]
  · intro a p row col hc
    have hb := routingScratch_bounds col hc
    have hn : ¬(111≤col ∧ col≤123) := by
      omega
    have h0 := hn
    simp only [characterAux,if_neg h0,ite_self]

theorem routing_length_commute (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    routingAux interval (characterLengthAux fallback)=characterLengthAux (routingAux interval fallback) := by
  apply routing_commute characterLengthAux
  · intro a b p row col he
    simp only [characterLengthAux,he]
  · intro a p row col hc
    have hb := routingScratch_bounds col hc
    have hn : ¬(xb 0≤col ∧ col<xb 6) ∧ ¬(xb 6≤col ∧ col<xb 12) := by
      simp only [xb]
      omega
    rcases hn with ⟨h0,h1⟩
    simp only [characterLengthAux,if_neg h0,if_neg h1,ite_self]

theorem routing_digest_commute (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    routingAux interval (digestMetadata fallback)=digestMetadata (routingAux interval fallback) := by
  apply routing_commute digestMetadata
  · intro a b p row col he
    simp only [digestMetadata,he]
  · intro a p row col hc
    have hb := routingScratch_bounds col hc
    have hn : col≠gDg ∧ col≠dI ∧ col≠dL := by
      simp only [gDg,dI,dL]
      omega
    rcases hn with ⟨h0,h1,h2⟩
    simp only [digestMetadata,if_neg h0,if_neg h1,if_neg h2,ite_self]

theorem routing_predecessor_commute (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    routingAux interval (predecessorAux fallback)=predecessorAux (routingAux interval fallback) := by
  apply routing_commute predecessorAux
  · intro a b p row col he
    simp only [predecessorAux,he]
  · intro a p row col hc
    have hb := routingScratch_bounds col hc
    have hn : col≠acc ∧ col≠p1 ∧ col≠isys := by
      simp only [acc,p1,isys]
      omega
    rcases hn with ⟨h0,h1,h2⟩
    simp only [predecessorAux,if_neg h0,if_neg h1,if_neg h2,ite_self]

theorem routing_named_commute (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    routingAux interval (namedAux fallback)=namedAux (routingAux interval fallback) := by
  apply routing_commute namedAux
  · intro a b p row col he
    simp only [namedAux,he]
  · intro a p row col hc
    have hb := routingScratch_bounds col hc
    have hn : col≠acc ∧ col≠vc0 ∧ col≠vc1 ∧ col≠h01 ∧ col≠p1 ∧ col≠p2 ∧ col≠p3 ∧ col≠i1 ∧ col≠i2 ∧ col≠i3 := by
      simp only [acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
      omega
    rcases hn with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    simp only [namedAux,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,ite_self]

theorem routing_system_commute (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (fallback : ReceiptPlan→Coord→Nat→Fp) :
    routingAux interval (systemAux fallback)=systemAux (routingAux interval fallback) := by
  apply routing_commute systemAux
  · intro a b p row col he
    simp only [systemAux,he]
  · intro a p row col hc
    have hb := routingScratch_bounds col hc
    have hn : col≠gV ∧ col≠gS ∧ col≠sx ∧ col≠invD ∧ col≠scnt ∧ col≠invL := by
      simp only [gV,gS,sx,invD,scnt,invL]
      omega
    rcases hn with ⟨h0,h1,h2,h3,h4,h5⟩
    simp only [systemAux,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,ite_self]

end ZkFormal.NearV3.Assembly.RcptSkeleton
