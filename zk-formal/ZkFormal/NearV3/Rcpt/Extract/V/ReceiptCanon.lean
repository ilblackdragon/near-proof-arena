import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptShape

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Routing lookup positions and the four received field values are canonical. -/
theorem routing_canon_of {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    ∀ e∈(rcptOf tr tt y).rlk, e.1<P ∧ e.2.1<P ∧ e.2.2.1<P ∧ e.2.2.2.1<P ∧ e.2.2.2.2<P := by
  intro e he
  simp only [rcptOf,List.mem_filterMap,List.mem_range] at he
  obtain ⟨k,hk,he⟩ := he
  split at he
  · cases he
    refine ⟨?_,cv_lt _ _ _ _,cv_lt _ _ _ _,cv_lt _ _ _ _,cv_lt _ _ _ _⟩
    have hfin := h.fin
    have hp := hP hL
    unfold total Vt at hfin
    split at hfin <;> omega
  · cases he

/-- Every raw V3 receipt value, including routing and system metadata, is canonical. -/
theorem raw3_canon_of {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) :
    ∀ v∈(rcptOf tr tt y).raw3, v<P := by
  intro v hv
  simp only [RcptE.raw3,List.mem_append] at hv
  rcases hv with ((hv|hv)|hv)|hv
  · exact raw_canon_of hL h v hv
  · exact colAt_lt _ _ _ _ _ _ hv
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl <;> exact cv_lt _ _ _ _
  · obtain ⟨e,he,hv⟩ := List.mem_flatMap.mp hv
    have hc := routing_canon_of hL h e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl
    · exact hc.1
    · exact hc.2.1
    · exact hc.2.2.1
    · exact hc.2.2.2.1
    · exact hc.2.2.2.2

/-- The full concrete table-view canonicity field follows from actual local constraints. -/
theorem ListChain.view_canon {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    (∀ L∈bs.map (ListBlock.view tr tt), L.n0<P ∧ L.n1<P) ∧
    ∀ x∈flatR (bs.map (ListBlock.view tr tt)), ∀ v∈x.raw3, v<P := by
  refine ⟨(h.view_header_facts hL).2.2,?_⟩
  intro x hx v hv
  simp only [flatR,List.mem_flatMap,List.mem_map] at hx
  obtain ⟨L,⟨B,hB,rfl⟩,hx⟩ := hx
  change x∈B.receipts.map (rcptOf tr tt) at hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  exact raw3_canon_of hL ((h.blocks B hB).layouts y hy) v hv

end ZkFormal.NearV3.RcptV3Proof
