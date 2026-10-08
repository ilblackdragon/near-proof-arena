import ZkFormal.NearV3.Rcpt.Candidates.CompactRootCells

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Render.UpsRelay UpsRows

theorem compact_instance_midroot (Is : List UpsInst) (i : Nat)
    (pos : RK→Nat) (next : RK→URow) (hl : (inst Is i).post.length=32) :
    (compactRecsI (inst Is i)).flatMap (fun rk=>
      compactMsgs (compactGeneratedRow Is (pos rk) (i,rk)) (next rk) B_ROOT true)=
      [reduceMessage ([(inst Is i).tau+1]++(inst Is i).post)] := by
  simp only [compact_root_row Is _ i _ _ hl,compactRecsI,List.flatMap_append,List.flatMap_map,List.flatMap_assoc]
  have hz {α : Type} (xs : List α) : xs.flatMap (fun _=>([] : List ZkFormal.Near.Msg))=[] := by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>simpa using ih
  simp [List.range_succ,hz]

theorem compact_root_inventory (Is : List UpsInst) (pos : Nat×RK→Nat) (next : Nat×RK→URow)
    (hl : ∀I∈Is,I.post.length=32) :
    (compactRecs Is).flatMap (fun r=>compactMsgs (compactGeneratedRow Is (pos r) r) (next r) B_ROOT true)=
      (Is.map (fun I=>[I.tau+1]++I.post)).map reduceMessage := by
  simp only [compactRecs,List.flatMap_assoc,List.flatMap_map]
  have he : ∀i∈List.range Is.length,
      (compactRecsI (inst Is i)).flatMap (fun rk=>
        compactMsgs (compactGeneratedRow Is (pos (i,rk)) (i,rk)) (next (i,rk)) B_ROOT true)=
      [reduceMessage ([(inst Is i).tau+1]++(inst Is i).post)] := by
    intro i hi
    apply compact_instance_midroot
    apply hl
    have hib:=List.mem_range.mp hi
    simp only [inst,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hib,Option.getD_some]
    exact List.getElem_mem hib
  rw [UpsRows.flatMap_congr' he]
  simp only [←List.map_eq_flatMap,List.map_map]
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.length_map] at hj
  simp only [List.getElem_map,List.getElem_range,inst,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
