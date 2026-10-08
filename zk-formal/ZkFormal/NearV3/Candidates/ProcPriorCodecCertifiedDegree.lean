import ZkFormal.NearV3.Candidates.ProcPriorCodecCertifiedProfile
import ZkFormal.NearV3.Candidates.InteractionTriplesDegree
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecActualFamily
open ZkFormal.Air HorizontalProfile
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem selected_constraints : ∀T∈selected,∀e∈T.allConstraints,e.degree≤8 := by
  have h:selected.all (fun T=>T.allConstraints.all (fun e=>decide (e.degree≤8)))=true := by decide +kernel
  exact fun T hT e he=>of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h T hT) e he)

theorem fused_constraints : ∀e∈fused.allConstraints,e.degree≤8 :=
  InteractionTriples.fused_paired_constraint_bound ProcPriorCodecActualFamily.selected 8
    ProcPriorCodecActualFamily.selected_constraints

theorem fused_degree : fused.degree 3=8 :=
  InteractionTriples.degree_eq fused 3 8 (by decide) fused_constraints fused_aux

theorem fused_shape : ZkFormal.Size.shapeOf 3 fused=⟨3402,90,7,90,22⟩ :=
  InteractionTriples.shape_eq fused 3 3402 90 8 114 156 22
    fused_width fused_aux_count fused_degree fused_sends fused_recvs rfl
end ZkFormal.NearV3.Candidates.ProcPriorCodecActualFamily
