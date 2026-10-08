import ZkFormal.NearV3.Candidates.ProcPriorFourStageLinearFusion
namespace ZkFormal.NearV3.Candidates.ProcPriorFourStageLinearFusion
open ZkFormal.Air
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
theorem selected_constraints : ∀T∈selected, ∀e∈T.allConstraints,e.degree≤8 := by
  intro T hT
  rcases List.mem_or_eq_of_mem_set hT with hT|rfl
  · rcases List.mem_or_eq_of_mem_set hT with hT|rfl
    · rcases List.mem_or_eq_of_mem_set hT with hT|rfl
      · rcases List.mem_append.mp hT with hT|hT
        · intro e he
          exact of_decide_eq_true (List.all_eq_true.mp
            (List.all_eq_true.mp GatedLengthFusion.selected_constraints T (List.mem_of_mem_take hT)) e he)
        · have ht:T=ProcPriorVertical.table:=List.mem_singleton.mp hT
          subst T
          have h:ProcPriorVertical.table.allConstraints.all (fun e=>decide (e.degree≤8))=true:=by decide +kernel
          exact fun e he=>of_decide_eq_true (List.all_eq_true.mp h e he)
      · have h:Rcpt.Candidates.EmptyValueFusion.valueTable.allConstraints.all (fun e=>decide (e.degree≤8))=true:=by decide +kernel
        exact fun e he=>of_decide_eq_true (List.all_eq_true.mp h e he)
    · have h:ProcPriorCodecParameter.table.allConstraints.all (fun e=>decide (e.degree≤8))=true:=by decide +kernel
      exact fun e he=>of_decide_eq_true (List.all_eq_true.mp h e he)
  · have h:ProcPriorVertical4Linear.table.allConstraints.all (fun e=>decide (e.degree≤8))=true:=by decide +kernel
    exact fun e he=>of_decide_eq_true (List.all_eq_true.mp h e he)

end ZkFormal.NearV3.Candidates.ProcPriorFourStageLinearFusion
