import ZkFormal.NearV3.Assembly.RcptNamedInversePhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem named_character_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    namedAux (characterAux fallback)=characterAux (namedAux fallback) := by
  funext p row col
  by_cases hs : row.state=sV
  · by_cases hc : col∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [namedAux,characterAux,hs,acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
    · have hh : ∀x∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3],col≠x := by grind only
      simp only [namedAux,characterAux,if_pos hs,if_neg (hh acc (by decide)),if_neg (hh vc0 (by decide)),if_neg (hh vc1 (by decide)),if_neg (hh h01 (by decide)),if_neg (hh p1 (by decide)),if_neg (hh p2 (by decide)),if_neg (hh p3 (by decide)),if_neg (hh i1 (by decide)),if_neg (hh i2 (by decide)),if_neg (hh i3 (by decide))]
  · simp only [namedAux,characterAux,if_neg hs]

theorem named_length_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    namedAux (characterLengthAux fallback)=characterLengthAux (namedAux fallback) := by
  funext p row col
  by_cases hs : row.state=sV
  · by_cases hc : col∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [namedAux,characterLengthAux,hs,acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3,xb]
    · have hh : ∀x∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3],col≠x := by grind only
      simp only [namedAux,characterLengthAux,if_pos hs,if_neg (hh acc (by decide)),if_neg (hh vc0 (by decide)),if_neg (hh vc1 (by decide)),if_neg (hh h01 (by decide)),if_neg (hh p1 (by decide)),if_neg (hh p2 (by decide)),if_neg (hh p3 (by decide)),if_neg (hh i1 (by decide)),if_neg (hh i2 (by decide)),if_neg (hh i3 (by decide))]
  · simp only [namedAux,characterLengthAux,if_neg hs]

theorem named_digest_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    namedAux (digestMetadata fallback)=digestMetadata (namedAux fallback) := by
  funext p row col
  by_cases hs : row.state=sV
  · by_cases hc : col∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [namedAux,digestMetadata,hs,acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3,gDg,dI,dL]
    · have hh : ∀x∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3],col≠x := by grind only
      simp only [namedAux,digestMetadata,if_pos hs,if_neg (hh acc (by decide)),if_neg (hh vc0 (by decide)),if_neg (hh vc1 (by decide)),if_neg (hh h01 (by decide)),if_neg (hh p1 (by decide)),if_neg (hh p2 (by decide)),if_neg (hh p3 (by decide)),if_neg (hh i1 (by decide)),if_neg (hh i2 (by decide)),if_neg (hh i3 (by decide))]
  · simp only [namedAux,digestMetadata,if_neg hs]

end ZkFormal.NearV3.Assembly.RcptSkeleton
