import ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
import ZkFormal.NearV3.Candidates.InteractionTriplesProfile
import ZkFormal.NearV3.Candidates.ProcPriorFourStageBounds
namespace ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
open ZkFormal.Air HorizontalProfile
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000


theorem fused_profiles : profiles fused=InteractionTriplesProfile.reorder
    (InteractionTriplesProfile.pairReorder (ProcPriorComparatorRoutedFamily.selected.flatMap profiles)) := by
  rw [fused,InteractionTriplesProfile.table_profiles]
  change (InteractionTriplesProfile.reorder
    ((InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions).map profile))=_
  rw [InteractionTriplesProfile.pairReorder_map]
  change (InteractionTriplesProfile.reorder (InteractionTriplesProfile.pairReorder
    (profiles (HorizontalTables.fuse ProcPriorComparatorRoutedFamily.selected))))=_
  rw [fuse_profiles]

theorem fused_width : fused.width=3402 := by decide +kernel

theorem fused_aux : fused.auxDegree 3=8 := by
  rw [auxDegree_eq,fused_profiles]
  decide +kernel

theorem fused_aux_count : fused.auxCount 3=90 := by
  rw [auxCount_eq,fused_profiles]
  decide +kernel

theorem fused_sends : fused.numSide true=114 := by
  rw [numSide_eq,fused_profiles]
  decide +kernel

theorem fused_recvs : fused.numSide false=156 := by
  rw [numSide_eq,fused_profiles]
  decide +kernel
end ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
