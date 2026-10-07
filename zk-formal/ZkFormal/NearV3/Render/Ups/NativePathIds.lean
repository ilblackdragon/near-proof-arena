import ZkFormal.NearV3.Render.Ups.TreePathChain

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem sourceLevelIds_proper (recordId : PTrie→Nat) (run : TreeRun) (level : Nat)
    (p : TreePart) (hp : (properPath run)[level]?=some p) :
    (sourceLevelIds recordId run).getD level 0=recordId p.source := by
  have hl : level<(properPath run).length := (List.getElem?_eq_some_iff.mp hp).1
  change (((properPath run).map (fun p => recordId p.source))++[recordId run.terminalSource]).getD level 0=_
  have hlm : level<((properPath run).map (fun p => recordId p.source)).length := by simpa using hl
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_left hlm,List.getElem?_map,hp]
  rfl

theorem sourceLevelIds_resolvedChild (recordId : PTrie→Nat) {root : PTrie} {key : List Nat}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root key v=some run) (level : Nat)
    (p : TreePart) (hp : (properPath run)[level]?=some p) (child : PTrie)
    (hc : sourcePathChild p=some child) :
    (sourceLevelIds recordId run).getD (level+1) 0=resolvedRecordId recordId child := by
  have hlink := traceUpsert_pathChain root key v run hr level p hp
  simp only [hc,Option.map_some] at hlink
  rw [←nativePathNodes_ids,List.getD_eq_getElem?_getD,List.getElem?_map,←hlink]
  rfl

theorem properSource_child {p : TreePart} (hs : ProperSource p) (hd : descendKind p.kind=true) :
    ∃ child,sourcePathChild p=some child := by
  cases hk : p.kind <;> simp only [hk,descendKind] at hd
  all_goals try contradiction
  · obtain ⟨value,kids,mem,child,cm,hsrc,hchild,_⟩ :=
      (show ∃ value kids mem child cm,p.source=.branch value kids mem ∧
        nativeChildAt kids p.slot=some child ∧ child.mem?=some cm by simpa [ProperSource,hk] using hs)
    exact ⟨child,by simpa [sourcePathChild,hsrc] using hchild⟩
  · obtain ⟨key,child,mem,cm,hsrc,_,_⟩ :=
      (show ∃ key child mem cm,p.source=.ext key child mem ∧ key≠[] ∧ child.mem?=some cm by
        simpa [ProperSource,hk] using hs)
    exact ⟨child,by simp [sourcePathChild,hsrc]⟩

theorem properPath_mem {run : TreeRun} {level : Nat} {p : TreePart}
    (hp : (properPath run)[level]?=some p) : p∈run.parts ∧ descendKind p.kind=true := by
  have hm := List.mem_of_getElem? hp
  simpa only [properPath,List.mem_reverse,List.mem_filter] using hm

/-- With the executable resolver, every proper ancestor edge targets exactly the
next generated source level, or stays at the same level before its final nibble. -/
theorem partWalkTarget_sourceLevels (recordId : PTrie→Nat) {root : PTrie} {key : List Nat}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root key v=some run) (level : Nat)
    (p : TreePart) (hp : (properPath run)[level]?=some p) (i : Nat) :
    partWalkTarget recordId (resolvedRecordId recordId) p i=
      if i+1=(partWalkKey p).length then ((sourceLevelIds recordId run).getD (level+1) 0,0)
      else ((sourceLevelIds recordId run).getD level 0,i+1) := by
  have hm := properPath_mem hp
  have hs := traceUpsert_properSources root key v run hr p hm.1
  obtain ⟨child,hc⟩ := properSource_child hs hm.2
  simp only [partWalkTarget,hc,Option.map_some,sourceLevelIds_proper recordId run level p hp,
    sourceLevelIds_resolvedChild recordId hr level p hp child hc]
end ZkFormal.NearV3.Render.UpsGen
