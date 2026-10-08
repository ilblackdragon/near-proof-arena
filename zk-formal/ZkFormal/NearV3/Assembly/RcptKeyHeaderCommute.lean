import ZkFormal.NearV3.Assembly.RcptKeyCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem key_header_digest_commute (fallback : ListPlan→Coord→Nat→Fp) :
    keyHeaderAux (digestHeaderMetadata fallback)=digestHeaderMetadata (keyHeaderAux fallback) := by
  funext p row col
  by_cases hc : col∈[gKA,gKB,kz,gF,gAK]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals rfl
  · simp only [keyHeaderAux,digestHeaderMetadata,if_neg hc]

theorem key_header_system_commute (fallback : ListPlan→Coord→Nat→Fp) :
    keyHeaderAux (systemHeaderAux fallback)=systemHeaderAux (keyHeaderAux fallback) := by
  funext p row col
  by_cases hc : col∈[gKA,gKB,kz,gF,gAK]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals rfl
  · simp only [keyHeaderAux,systemHeaderAux,if_neg hc]

theorem key_header_routing_commute (fallback : ListPlan→Coord→Nat→Fp) :
    keyHeaderAux (routingHeaderAux fallback)=routingHeaderAux (keyHeaderAux fallback) := by
  funext p row col
  by_cases hc : col∈[gKA,gKB,kz,gF,gAK]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl
    all_goals rfl
  · simp only [keyHeaderAux,routingHeaderAux,if_neg hc]

end ZkFormal.NearV3.Assembly.RcptSkeleton
