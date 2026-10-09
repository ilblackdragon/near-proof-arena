import ZkFormal.NearV3.Render.Ups.NativePrefixZero

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

theorem nativePathNodes_proper (run : TreeRun) (level : Nat) (p : TreePart)
    (hp : (properPath run)[level]?=some p) : (nativePathNodes run)[level]?=some p.source := by
  have hl : level<(properPath run).length := (List.getElem?_eq_some_iff.mp hp).1
  change ((properPath run).map TreePart.source++[run.terminalSource])[level]?=_
  have hlm : level<((properPath run).map TreePart.source).length := by simpa using hl
  rw [List.getElem?_append_left hlm,List.getElem?_map,hp]
  rfl

theorem nativePathEdgeKind_proper {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (level : Nat) (p : TreePart)
    (hp : (properPath run)[level]?=some p) :
    nativePathEdgeKind run level=if p.kind=.RDB then EK_DOWN else EK_KEY := by
  have hm := properPath_mem hp
  have hs := traceUpsert_properSources root key v run hr p hm.1
  rw [nativePathEdgeKind,nativePathNodes_proper run level p hp]
  have hd := hm.2
  cases hk : p.kind <;> simp only [hk,descendKind] at hd
  all_goals try contradiction
  · obtain ⟨value,kids,mem,child,cm,hsrc,_,_⟩ :=
      (show ∃ value kids mem child cm,p.source=.branch value kids mem ∧
        nativeChildAt kids p.slot=some child ∧ child.mem?=some cm by simpa [ProperSource,hk] using hs)
    simp [hsrc,hk]
  · obtain ⟨key,child,mem,cm,hsrc,_,_⟩ :=
      (show ∃ key child mem cm,p.source=.ext key child mem ∧ key≠[] ∧ child.mem?=some cm by
        simpa [ProperSource,hk] using hs)
    simp [hsrc,hk]

theorem nativePathEdgeKind_terminal {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (hfind : root.find key≠none) (hm : 0<run.matched) :
    nativePathEdgeKind run (descentCount run.parts)=EK_KEY := by
  have hn : (nativePathNodes run)[descentCount run.parts]?=some run.terminalSource := by
    simp [nativePathNodes,descentCount,List.getElem?_append]
  rw [nativePathEdgeKind,hn]
  rcases traceUpsert_terminalNodeShape hr hfind with ⟨key,slot,mem,hs⟩|⟨key,child,mem,hs,_⟩|hzero
  · simp [hs]
  · simp [hs]
  · omega

theorem partWalkEdge_sourceLevels (recordId : PTrie→Nat) {root : PTrie} {key : List Nat}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert root key v=some run) (level : Nat)
    (p : TreePart) (hp : (properPath run)[level]?=some p) (i : Nat) :
    partWalkEdge recordId (resolvedRecordId recordId) p i=
      [(sourceLevelIds recordId run).getD level 0,i,(partWalkKey p).getD i 0,
        if i+1=(partWalkKey p).length then (sourceLevelIds recordId run).getD (level+1) 0
          else (sourceLevelIds recordId run).getD level 0,
        if i+1=(partWalkKey p).length then 0 else i+1,nativePathEdgeKind run level] := by
  rw [partWalkEdge,partWalkTarget_sourceLevels recordId hr level p hp,
    sourceLevelIds_proper recordId run level p hp,nativePathEdgeKind_proper hr level p hp]
  split <;> rfl
end ZkFormal.NearV3.Render.UpsGen
