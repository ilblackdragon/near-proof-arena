import ZkFormal.NearV3.Render.Ups.NativePrefixTwo

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

/-- The source annotation is executable for every actual revealed node. -/
theorem nativePathNode_total (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat)
    (source : PTrie) (hs : isNode source=true) :
    ∃ node,nativePathNode recordId resolvedId valueId source=some node := by
  cases source with
  | hash => simp [isNode] at hs
  | leaf | ext | branch => exact ⟨_,rfl⟩

/-- Each explicit native prefix edge has a concrete source-node provider. This is local
source annotation; locating the same provider in the global occurrence store is separate. -/
theorem nativePrefixEdges_provider (recordId : PTrie→Nat) (valueId : Slot→Nat)
    {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (hfind : root.find key≠none)
    (edge : List Nat) (he : edge∈nativePrefixEdges recordId run) :
    ∃ source node,nativePathNode recordId (resolvedRecordId recordId) valueId source=some node ∧
      edge∈edgesOf3 (recordId source) {(default : NodeS3) with v:=node} := by
  simp only [nativePrefixEdges,List.mem_append] at he
  rcases he with he|he
  · obtain ⟨p,hp,he⟩ := List.mem_flatMap.mp he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    have hm : p∈run.parts ∧ descendKind p.kind=true := by
      simpa only [properPath,List.mem_reverse,List.mem_filter] using hp
    have hs := (traceUpsert_nodeParts root key v run hr p hm.1).1
    obtain ⟨node,hn⟩ := nativePathNode_total recordId (resolvedRecordId recordId) valueId p.source hs
    refine ⟨p.source,node,hn,?_⟩
    exact nativePathNode_proper_edge recordId (resolvedRecordId recordId) valueId hr p hm.1 hm.2 i
      (List.mem_range.mp hi) {(default : NodeS3) with v:=node} hn
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    have hi' : i<run.matched := List.mem_range.mp hi
    have hs : isNode run.terminalSource=true := by
      rcases traceUpsert_terminalNodeShape hr hfind with ⟨key,slot,mem,hs⟩|⟨key,child,mem,hs,_⟩|hz
      · rw [hs]; rfl
      · rw [hs]; rfl
      · omega
    obtain ⟨node,hn⟩ := nativePathNode_total recordId (resolvedRecordId recordId) valueId run.terminalSource hs
    refine ⟨run.terminalSource,node,hn,?_⟩
    exact nativePathNode_terminal_prefix_edge recordId (resolvedRecordId recordId) valueId hr hfind i hi'
      {(default : NodeS3) with v:=node} hn

/-- Every physical pre-terminal update walk row has its checked concrete native provider. -/
theorem nativeInstance_prefix_provider (recordId : PTrie→Nat) (valueId : Slot→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hfind : root.find [0,15]≠none) (Qs : List UpsPartI) (t : Nat) :
    let I := nativeInstance recordId
      (nativeWalkBase recordId valueId (resolvedRecordId recordId) baseI root run v) root run v Qs
    1≤t → t<I.ts → ∃ source node,
      nativePathNode recordId (resolvedRecordId recordId) valueId source=some node ∧
      (step I t).e∈edgesOf3 (recordId source) {(default : NodeS3) with v:=node} := by
  dsimp only
  intro ht hts
  let I := nativeInstance recordId
    (nativeWalkBase recordId valueId (resolvedRecordId recordId) baseI root run v) root run v Qs
  change t<I.ts at hts
  have he : (step I t).e∈nativePhysicalPrefixEdges recordId valueId baseI root run v Qs := by
    change (step I t).e∈(List.range (I.ts-1)).map (fun i => (step I (i+1)).e)
    exact List.mem_map.mpr ⟨t-1,List.mem_range.mpr (by omega),by rw [Nat.sub_add_cancel ht]⟩
  rw [←nativePrefixEdges_physical recordId valueId baseI hr hfind Qs] at he
  exact nativePrefixEdges_provider recordId valueId hr hfind _ he

/-- W0 targets exactly the resolved native root, the target required of its START provider. -/
theorem nativeInstance_start_edge (recordId : PTrie→Nat) (valueId : Slot→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (Qs : List UpsPartI) :
    (step (nativeInstance recordId
      (nativeWalkBase recordId valueId (resolvedRecordId recordId) baseI root run v) root run v Qs) 0).e=
      [0,baseI.tau,SYM_START,resolvedRecordId recordId root,0,EK_DOWN] := by
  change [0,baseI.tau,SYM_START,(sourceLevelIds recordId run).getD 0 0,0,EK_DOWN]=_
  rw [sourceLevelIds_resolvedRoot recordId hr]
end ZkFormal.NearV3.Render.UpsGen
