import ZkFormal.NearV3.Render.Ups.NativePrefixEdges

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

/-- Physical pre-terminal rows of the constructed four-row native walk. -/
def nativePhysicalPrefixEdges (recordId : PTrie→Nat) (valueId : Slot→Nat) (baseI : UpsInst)
    (root : PTrie) (run : TreeRun) (v : Bytes) (Qs : List UpsPartI) : List (List Nat) :=
  let I := nativeInstance recordId
    (nativeWalkBase recordId valueId (resolvedRecordId recordId) baseI root run v) root run v Qs
  (List.range (I.ts-1)).map fun i => (step I (i+1)).e

/-- With no proper ancestor, physical W1/W2 are precisely the native terminal-record
prefix edges. Empty extensions above that record are already removed by resolution. -/
theorem nativePrefixEdges_zero (recordId : PTrie→Nat) (valueId : Slot→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hfind : root.find [0,15]≠none) (hpath : properPath run=[]) (Qs : List UpsPartI) :
    nativePrefixEdges recordId run=nativePhysicalPrefixEdges recordId valueId baseI root run v Qs := by
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget valueId (resolvedRecordId recordId) run (recordId run.terminalSource)
  change nativePrefixEdges recordId run=(List.range (I.ts-1)).map fun i =>
    (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
      (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2) (i+1)).e
  have hnodes : nativePathNodes run=[run.terminalSource] := by
    change (properPath run).map TreePart.source++[run.terminalSource]=_
    rw [hpath]; rfl
  have hn : I.N=[recordId run.terminalSource] := by
    change sourceLevelIds recordId run=_
    rw [←nativePathNodes_ids,hnodes]; rfl
  have hd : I.D=0 := by
    change descentCount run.parts=0
    have hh := congrArg List.length hpath
    simpa only [properPath,List.length_reverse,descentCount,List.length_nil] using hh
  have hk : run.terminalKey=[0,15] := by
    have hq := traceUpsert_walkQuery root [0,15] v run hr
    change (properPath run).flatMap partWalkKey++run.terminalKey=[0,15] at hq
    simpa only [hpath,List.flatMap_nil,List.nil_append] using hq
  have ht : I.ts=run.matched+1 := by
    change run.splitCursor [0,15]=_
    simp [TreeRun.splitCursor,TreeRun.consumed,hk]
  have hi : I.ti=run.matched := rfl
  have he : 0<run.matched → nativePathEdgeKind run 0=EK_KEY := by
    intro hm
    rcases traceUpsert_terminalNodeShape hr hfind with ⟨key,slot,mem,hs⟩|⟨key,child,mem,hs,_⟩|hzero
    · simp [nativePathEdgeKind,hnodes,hs]
    · simp [nativePathEdgeKind,hnodes,hs]
    · omega
  have hb := (trace_fixedKey_bounds hr).2.1
  rcases (show run.matched=0 ∨ run.matched=1 ∨ run.matched=2 by omega) with hm|hm|hm
  · simp [nativePrefixEdges,ancestorWalkEdges,terminalWalkEdges,hpath,hm,ht]
  · have he' := he (by omega)
    simp [nativePrefixEdges,ancestorWalkEdges,terminalWalkEdges,hpath,hm,ht,hd,hn,hi,hk,
      step,withFourWalk,fourWalk,walkEnter1,he',List.range_succ]
  · have he' := he (by omega)
    simp [nativePrefixEdges,ancestorWalkEdges,terminalWalkEdges,hpath,hm,ht,hd,hn,hi,hk,
      step,withFourWalk,fourWalk,walkEnter1,he',List.range_succ]
end ZkFormal.NearV3.Render.UpsGen
