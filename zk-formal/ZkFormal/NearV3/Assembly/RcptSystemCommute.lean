import ZkFormal.NearV3.Assembly.RcptSystemCounterPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem system_character_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    systemAux (characterAux fallback)=characterAux (systemAux fallback) := by
  funext p row col
  by_cases hc : col∈[gV,gS,sx,invD,scnt,invL]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [characterAux,systemAux,gV,gS,sx,invD,scnt,invL]
  · have hh : ∀x∈[gV,gS,sx,invD,scnt,invL],col≠x := by grind only
    simp only [systemAux,characterAux,if_neg (hh gV (by decide)),if_neg (hh gS (by decide)),if_neg (hh sx (by decide)),if_neg (hh invD (by decide)),if_neg (hh scnt (by decide)),if_neg (hh invL (by decide))]

theorem system_length_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    systemAux (characterLengthAux fallback)=characterLengthAux (systemAux fallback) := by
  funext p row col
  by_cases hc : col∈[gV,gS,sx,invD,scnt,invL]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [characterLengthAux,systemAux,gV,gS,sx,invD,scnt,invL,xb]
  · have hh : ∀x∈[gV,gS,sx,invD,scnt,invL],col≠x := by grind only
    simp only [systemAux,characterLengthAux,if_neg (hh gV (by decide)),if_neg (hh gS (by decide)),if_neg (hh sx (by decide)),if_neg (hh invD (by decide)),if_neg (hh scnt (by decide)),if_neg (hh invL (by decide))]

theorem system_digest_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    systemAux (digestMetadata fallback)=digestMetadata (systemAux fallback) := by
  funext p row col
  by_cases hc : col∈[gV,gS,sx,invD,scnt,invL]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [digestMetadata,systemAux,gV,gS,sx,invD,scnt,invL,gDg,dI,dL]
  · have hh : ∀x∈[gV,gS,sx,invD,scnt,invL],col≠x := by grind only
    simp only [systemAux,digestMetadata,if_neg (hh gV (by decide)),if_neg (hh gS (by decide)),if_neg (hh sx (by decide)),if_neg (hh invD (by decide)),if_neg (hh scnt (by decide)),if_neg (hh invL (by decide))]

theorem system_predecessor_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    systemAux (predecessorAux fallback)=predecessorAux (systemAux fallback) := by
  funext p row col
  by_cases hc : col∈[gV,gS,sx,invD,scnt,invL]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [predecessorAux,systemAux,gV,gS,sx,invD,scnt,invL,acc,p1,isys]
  · have hh : ∀x∈[gV,gS,sx,invD,scnt,invL],col≠x := by grind only
    simp only [systemAux,predecessorAux,if_neg (hh gV (by decide)),if_neg (hh gS (by decide)),if_neg (hh sx (by decide)),if_neg (hh invD (by decide)),if_neg (hh scnt (by decide)),if_neg (hh invL (by decide))]

theorem system_named_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    systemAux (namedAux fallback)=namedAux (systemAux fallback) := by
  funext p row col
  by_cases hc : col∈[gV,gS,sx,invD,scnt,invL]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [namedAux,systemAux,gV,gS,sx,invD,scnt,invL,acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]
  · have hh : ∀x∈[gV,gS,sx,invD,scnt,invL],col≠x := by grind only
    simp only [systemAux,namedAux,if_neg (hh gV (by decide)),if_neg (hh gS (by decide)),if_neg (hh sx (by decide)),if_neg (hh invD (by decide)),if_neg (hh scnt (by decide)),if_neg (hh invL (by decide))]

theorem system_header_character_commute (fallback : ListPlan→Coord→Nat→Fp) :
    systemHeaderAux (characterHeaderAux fallback)=characterHeaderAux (systemHeaderAux fallback) := by
  funext p row col
  by_cases hc : col=gV ∨ col=gS
  · rcases hc with rfl|rfl <;> simp [systemHeaderAux,characterHeaderAux,gV,gS]
  · simp only [systemHeaderAux,characterHeaderAux,if_neg hc]

theorem system_header_digest_commute (fallback : ListPlan→Coord→Nat→Fp) :
    systemHeaderAux (digestHeaderMetadata fallback)=digestHeaderMetadata (systemHeaderAux fallback) := by
  funext p row col
  by_cases hc : col=gV ∨ col=gS
  · rcases hc with rfl|rfl <;> simp [systemHeaderAux,digestHeaderMetadata,gV,gS,gDg]
  · simp only [systemHeaderAux,digestHeaderMetadata,if_neg hc]

end ZkFormal.NearV3.Assembly.RcptSkeleton
