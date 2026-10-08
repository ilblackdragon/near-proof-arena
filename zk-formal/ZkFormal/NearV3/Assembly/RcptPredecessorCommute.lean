import ZkFormal.NearV3.Assembly.RcptPredecessorStepPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem predecessor_character_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    predecessorAux (characterAux fallback)=characterAux (predecessorAux fallback) := by
  funext p row col
  by_cases hs : row.state=sP
  · by_cases h1 : col=acc
    · subst col; simp [predecessorAux,characterAux,hs,acc,p1,isys]
    · by_cases h2 : col=p1
      · subst col; simp [predecessorAux,characterAux,hs,acc,p1,isys]
      · by_cases h3 : col=isys
        · subst col; simp [predecessorAux,characterAux,hs,acc,p1,isys]
        · simp only [predecessorAux,characterAux,if_pos hs,if_neg h1,if_neg h2,if_neg h3]
  · simp only [predecessorAux,characterAux,if_neg hs]

theorem predecessor_length_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    predecessorAux (characterLengthAux fallback)=characterLengthAux (predecessorAux fallback) := by
  funext p row col
  by_cases hs : row.state=sP
  · by_cases h1 : col=acc
    · subst col; simp [predecessorAux,characterLengthAux,hs,acc,p1,isys,xb]
    · by_cases h2 : col=p1
      · subst col; simp [predecessorAux,characterLengthAux,hs,acc,p1,isys,xb]
      · by_cases h3 : col=isys
        · subst col; simp [predecessorAux,characterLengthAux,hs,acc,p1,isys,xb]
        · simp only [predecessorAux,characterLengthAux,if_pos hs,if_neg h1,if_neg h2,if_neg h3]
  · simp only [predecessorAux,characterLengthAux,if_neg hs]

theorem predecessor_digest_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    predecessorAux (digestMetadata fallback)=digestMetadata (predecessorAux fallback) := by
  funext p row col
  by_cases hs : row.state=sP
  · by_cases h1 : col=acc
    · subst col; simp [predecessorAux,digestMetadata,hs,acc,p1,isys,gDg,dI,dL]
    · by_cases h2 : col=p1
      · subst col; simp [predecessorAux,digestMetadata,hs,acc,p1,isys,gDg,dI,dL]
      · by_cases h3 : col=isys
        · subst col; simp [predecessorAux,digestMetadata,hs,acc,p1,isys,gDg,dI,dL]
        · simp only [predecessorAux,digestMetadata,if_pos hs,if_neg h1,if_neg h2,if_neg h3]
  · simp only [predecessorAux,digestMetadata,if_neg hs]

end ZkFormal.NearV3.Assembly.RcptSkeleton
