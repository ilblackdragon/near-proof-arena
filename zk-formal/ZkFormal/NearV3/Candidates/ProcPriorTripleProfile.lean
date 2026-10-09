import ZkFormal.NearV3.Candidates.ProcPriorTripleFusion
import ZkFormal.NearV3.Candidates.InteractionTriplesProfile
import ZkFormal.NearV3.Candidates.ProcPriorFourStageBounds
namespace ZkFormal.NearV3.Candidates.ProcPriorTripleFusion
open ZkFormal.Air HorizontalProfile
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

abbrev fused := InteractionTriples.table ProcPriorFourStageLinearFusion.table

theorem fused_profiles : profiles fused=InteractionTriplesProfile.reorder
    (InteractionTriplesProfile.pairReorder (ProcPriorFourStageLinearFusion.selected.flatMap profiles)) := by
  rw [InteractionTriplesProfile.table_profiles]
  change (InteractionTriplesProfile.reorder
    ((InteractionPairing.reorder ProcPriorFourStageLinearFusion.raw.interactions).map profile))=_
  rw [InteractionTriplesProfile.pairReorder_map]
  change (InteractionTriplesProfile.reorder (InteractionTriplesProfile.pairReorder
    (profiles (HorizontalTables.fuse ProcPriorFourStageLinearFusion.selected))))=_
  rw [fuse_profiles]

theorem fused_width : fused.width=3402 := by decide +kernel

theorem fused_aux : fused.auxDegree 3=8 := by
  rw [auxDegree_eq,fused_profiles]
  decide +kernel

theorem fused_aux_count : fused.auxCount 3=89 := by
  rw [auxCount_eq,fused_profiles]
  decide +kernel

theorem fused_sends : fused.numSide true=111 := by
  rw [numSide_eq,fused_profiles]
  decide +kernel

theorem fused_recvs : fused.numSide false=156 := by
  rw [numSide_eq,fused_profiles]
  decide +kernel
end ZkFormal.NearV3.Candidates.ProcPriorTripleFusion
