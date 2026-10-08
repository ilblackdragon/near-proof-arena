import ZkFormal.NearV3.Candidates.SortEmptyFamilyWf
namespace ZkFormal.NearV3.Candidates.SortEmptyFamily
open ZkFormal.Air ZkFormal.Size HorizontalProfile
open ProcPriorCodecActualFamily (fused)
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem mult_bound : air.multBound=1038721028 := by
  unfold Air.multBound
  change ((fused::rest.map InteractionTriples.table).map _).sum=_
  simp only [List.map_cons,List.sum_cons,mult_weights,ProcPriorCodecActualFamily.fused_profiles]
  decide +kernel



theorem fp_bound : air.fpBound=68697539256 := by
  unfold Air.fpBound
  change ((fused::rest.map InteractionTriples.table).map _).sum *
    (((fused::rest.map InteractionTriples.table).flatMap _).foldr max 0+1)=_
  simp only [List.map_cons,List.sum_cons,List.flatMap_cons,interaction_count,msg_lengths,ProcPriorCodecActualFamily.fused_profiles]
  decide +kernel



end ZkFormal.NearV3.Candidates.SortEmptyFamily
