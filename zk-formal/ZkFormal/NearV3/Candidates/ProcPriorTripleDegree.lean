import ZkFormal.NearV3.Candidates.ProcPriorTripleProfile
import ZkFormal.NearV3.Candidates.InteractionTriplesDegree
namespace ZkFormal.NearV3.Candidates.ProcPriorTripleFusion
open ZkFormal.Air HorizontalProfile
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem fused_constraints : ∀e∈fused.allConstraints,e.degree≤8 :=
  InteractionTriples.fused_paired_constraint_bound ProcPriorFourStageLinearFusion.selected 8
    ProcPriorFourStageLinearFusion.selected_constraints

theorem fused_degree : fused.degree 3=8 :=
  InteractionTriples.degree_eq fused 3 8 (by decide) fused_constraints fused_aux

theorem fused_shape : ZkFormal.Size.shapeOf 3 fused=⟨3402,89,7,89,22⟩ :=
  InteractionTriples.shape_eq fused 3 3402 89 8 111 156 22
    fused_width fused_aux_count fused_degree fused_sends fused_recvs rfl
end ZkFormal.NearV3.Candidates.ProcPriorTripleFusion
