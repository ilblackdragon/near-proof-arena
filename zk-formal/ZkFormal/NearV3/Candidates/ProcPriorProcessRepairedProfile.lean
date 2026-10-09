import ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedFamily
import ZkFormal.NearV3.Candidates.ProcPriorProcessTransport
import ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedProfile
import ZkFormal.NearV3.Candidates.InteractionTriplesProfile
import ZkFormal.NearV3.Candidates.ProcPriorFourStageBounds
namespace ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedFamily
open ZkFormal.Air HorizontalProfile
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000


theorem fused_profiles : profiles fused=InteractionTriplesProfile.reorder
    (InteractionTriplesProfile.pairReorder (ProcPriorProcessRepairedFamily.selected.flatMap profiles)) := by
  rw [fused,InteractionTriplesProfile.table_profiles]
  change (InteractionTriplesProfile.reorder
    ((InteractionPairing.reorder ProcPriorProcessRepairedFamily.raw.interactions).map profile))=_
  rw [InteractionTriplesProfile.pairReorder_map]
  change (InteractionTriplesProfile.reorder (InteractionTriplesProfile.pairReorder
    (profiles (HorizontalTables.fuse ProcPriorProcessRepairedFamily.selected))))=_
  rw [fuse_profiles]

theorem fused_width : fused.width=3402 := by decide +kernel

theorem fused_aux : fused.auxDegree 3=8 := by
  rw [auxDegree_eq]
  change _
  have he:profiles fused=profiles ProcPriorComparatorRoutedFamily.fused:=by
    unfold profiles
    rw [ProcPriorProcessTransport.fused_interactions]
  rw [he,←auxDegree_eq]
  exact ProcPriorComparatorRoutedFamily.fused_aux

theorem fused_aux_count : fused.auxCount 3=90 := by
  rw [auxCount_eq]
  change _
  have he:profiles fused=profiles ProcPriorComparatorRoutedFamily.fused:=by
    unfold profiles
    rw [ProcPriorProcessTransport.fused_interactions]
  rw [he,←auxCount_eq]
  exact ProcPriorComparatorRoutedFamily.fused_aux_count

theorem fused_sends : fused.numSide true=114 := by
  rw [numSide_eq]
  change _
  have he:profiles fused=profiles ProcPriorComparatorRoutedFamily.fused:=by
    unfold profiles
    rw [ProcPriorProcessTransport.fused_interactions]
  rw [he,←numSide_eq]
  exact ProcPriorComparatorRoutedFamily.fused_sends

theorem fused_recvs : fused.numSide false=156 := by
  rw [numSide_eq]
  change _
  have he:profiles fused=profiles ProcPriorComparatorRoutedFamily.fused:=by
    unfold profiles
    rw [ProcPriorProcessTransport.fused_interactions]
  rw [he,←numSide_eq]
  exact ProcPriorComparatorRoutedFamily.fused_recvs

end ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedFamily
