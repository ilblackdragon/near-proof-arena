import ZkFormal.NearV3.Assembly.RcptRoutingCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem routing_header_character_commute (fallback : ListPlan→Coord→Nat→Fp) :
    routingHeaderAux (characterHeaderAux fallback)=characterHeaderAux (routingHeaderAux fallback) := by
  funext p row col
  by_cases hc : col=gBd
  · subst col
    simp only [routingHeaderAux,characterHeaderAux,gBd,gV,gS,gDg,Nat.reduceEqDiff,Nat.reduceLeDiff,Nat.reduceLT,false_or,false_and,and_false,ite_true,ite_false]
  · simp only [routingHeaderAux,characterHeaderAux,if_neg hc]

theorem routing_header_digest_commute (fallback : ListPlan→Coord→Nat→Fp) :
    routingHeaderAux (digestHeaderMetadata fallback)=digestHeaderMetadata (routingHeaderAux fallback) := by
  funext p row col
  by_cases hc : col=gBd
  · subst col
    simp only [routingHeaderAux,digestHeaderMetadata,gBd,gV,gS,gDg,Nat.reduceEqDiff,Nat.reduceLeDiff,Nat.reduceLT,false_or,false_and,and_false,ite_true,ite_false]
  · simp only [routingHeaderAux,digestHeaderMetadata,if_neg hc]

theorem routing_header_system_commute (fallback : ListPlan→Coord→Nat→Fp) :
    routingHeaderAux (systemHeaderAux fallback)=systemHeaderAux (routingHeaderAux fallback) := by
  funext p row col
  by_cases hc : col=gBd
  · subst col
    simp only [routingHeaderAux,systemHeaderAux,gBd,gV,gS,gDg,Nat.reduceEqDiff,Nat.reduceLeDiff,Nat.reduceLT,false_or,false_and,and_false,ite_true,ite_false]
  · simp only [routingHeaderAux,systemHeaderAux,if_neg hc]

end ZkFormal.NearV3.Assembly.RcptSkeleton
