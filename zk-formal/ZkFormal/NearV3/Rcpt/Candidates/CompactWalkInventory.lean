import ZkFormal.NearV3.Rcpt.Candidates.CompactWalkRows

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

private theorem map_range_getD {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun i=>xs.getD i d)=xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map,List.getElem_range,List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj,Option.getD_some]

theorem compact_row_independent (Is : List UpsInst) (r : Nat×RK)
    (hr : r∈compactRecs Is) (q : Nat) (D : URow) (bus : Nat)
    (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    compactMsgs (compactGeneratedRow Is q r) D bus sd=
      compactMsgs (compactGeneratedRow Is 0 r) (fun _=>0) bus sd := by
  obtain ⟨hi,hm⟩:=compact_mem.mp hr
  rcases compact_mem_I.mp hm with ⟨t,ht,he⟩|⟨k,p,hk,hp,he⟩
  · have hr' : r=(r.1,.w t) := Prod.ext rfl he
    rw [hr',compact_walk_row Is _ _ _ _ bus hb sd,compact_walk_row Is _ _ _ _ bus hb sd]
  · have hr' : r=(r.1,.q k p) := Prod.ext rfl he
    rw [hr',compact_part_silent Is _ _ _ _ _ bus hb sd,compact_part_silent Is _ _ _ _ _ bus hb sd]

theorem compact_walk_inventory (Is : List UpsInst) (bus : Nat)
    (hb : bus=B_EDGE ∨ bus=B_BMAP) (sd : Bool) :
    (compactRecs Is).flatMap (fun r=>compactMsgs (compactGeneratedRow Is 0 r) (fun _=>0) bus sd)=
      upsWalkMessages Is bus sd := by
  simp only [compactRecs,List.flatMap_assoc,List.flatMap_map]
  have he : (List.range Is.length).flatMap (fun i=>
      (compactRecsI (inst Is i)).flatMap (fun r=>compactMsgs (compactGeneratedRow Is 0 (i,r)) (fun _=>0) bus sd))=
      (List.range Is.length).flatMap (fun i=>upsWalkMessages [inst Is i] bus sd) := by
    apply UpsRows.flatMap_congr'
    intro i hi
    exact compact_instance_traffic Is i (fun _=>0) (fun _ _=>0) bus hb sd
  rw [he]
  have hm:=congrArg (fun xs=>xs.flatMap (fun I=>upsWalkMessages [I] bus sd)) (map_range_getD Is default)
  simpa only [List.flatMap_map,inst,upsWalkMessages,List.flatMap_cons,List.flatMap_nil,List.append_nil] using hm

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
