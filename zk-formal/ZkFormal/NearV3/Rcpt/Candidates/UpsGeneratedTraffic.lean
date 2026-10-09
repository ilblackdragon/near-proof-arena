import ZkFormal.NearV3.Rcpt.Candidates.UpsSilentRows

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near Render.UpsGen UpsRows

/-- Every generated instance row is included; non-walk rows contribute zero. -/
theorem generated_instance_traffic (Is : List Render.UpsInst) (i : Nat)
    (pos : RK→Nat) (next : RK→URow) (bus : Nat)
    (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    ((recsI (inst Is i)).flatMap (fun r=>uMsgs (generatedRow Is (pos r) (i,r)) (next r) bus sd))=
      upsWalkMessages [inst Is i] bus sd := by
  simp only [recsI,List.flatMap_append,List.flatMap_map,List.flatMap_assoc]
  simp [walk_generated_interactions Is _ _ _ _ bus hb sd,
    value_interactions_silent Is _ _ _ _ bus hb sd,
    part_interactions_silent Is _ _ _ _ _ bus hb sd,List.flatMap_nil,
    List.append_nil]
  have hz {α : Type} (xs : List α) : xs.flatMap (fun _=>([] : List Msg))=[] := by
    induction xs with
    | nil=>rfl
    | cons a xs ih=>simpa using ih
  simp only [hz,List.append_nil]
  simp [upsWalkMessages,List.range_succ,List.ofFn_succ];rfl

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
