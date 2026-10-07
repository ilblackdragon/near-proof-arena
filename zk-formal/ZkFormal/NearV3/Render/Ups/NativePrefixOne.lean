import ZkFormal.NearV3.Render.Ups.NativePathKind

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

private theorem nonempty_append_two (xs ys : List Nat) (hn : xs≠[]) (he : xs++ys=[0,15]) :
    (xs=[0] ∧ ys=[15]) ∨ (xs=[0,15] ∧ ys=[]) := by
  cases xs with
  | nil => exact (hn rfl).elim
  | cons a xs =>
    cases xs with
    | nil => simpa using he
    | cons b xs =>
      simp only [List.cons_append,List.cons.injEq] at he
      have hz : xs=[] ∧ ys=[] := List.append_eq_nil_iff.mp he.2.2
      rcases hz with ⟨rfl,rfl⟩
      simp_all

/-- Physical prefix rows agree with the native edge sequence for a single proper ancestor. -/
theorem nativePrefixEdges_one (recordId : PTrie→Nat) (valueId : Slot→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hfind : root.find [0,15]≠none) (p : TreePart) (hpath : properPath run=[p]) (Qs : List UpsPartI) :
    nativePrefixEdges recordId run=nativePhysicalPrefixEdges recordId valueId baseI root run v Qs := by
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget valueId (resolvedRecordId recordId) run (recordId run.terminalSource)
  change nativePrefixEdges recordId run=(List.range (I.ts-1)).map fun i =>
    (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
      (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2) (i+1)).e
  have hpp : (properPath run)[0]?=some p := by simp [hpath]
  have hpm := properPath_mem hpp
  have hsrc := traceUpsert_properSources root [0,15] v run hr p hpm.1
  have hne := properSource_walkKey_nonempty hsrc hpm.2
  have hn0 : sourceLevelIds recordId run=[recordId p.source,recordId run.terminalSource] := by
    change (properPath run).map (fun p => recordId p.source)++[recordId run.terminalSource]=_
    rw [hpath]; rfl
  have hn : I.N=[recordId p.source,recordId run.terminalSource] := hn0
  have hdes : descentCount run.parts=1 := by
    have hh := congrArg List.length hpath
    simpa only [properPath,descentCount,List.length_reverse,List.length_singleton] using hh
  have hd : I.D=1 := hdes
  have hi : I.ti=run.matched := rfl
  have hq : partWalkKey p++run.terminalKey=[0,15] := by
    have hq := traceUpsert_walkQuery root [0,15] v run hr
    change (properPath run).flatMap partWalkKey++run.terminalKey=[0,15] at hq
    simpa [hpath] using hq
  obtain ⟨_,_,_,hmatched⟩ := traceUpsert_keys root [0,15] v run hr
  have he := fun i => partWalkEdge_sourceLevels recordId hr 0 p hpp i
  rcases nonempty_append_two (partWalkKey p) run.terminalKey hne hq with ⟨hseg,hkey⟩|⟨hseg,hkey⟩
  · have hm : run.matched=0 ∨ run.matched=1 := by simp only [hkey,List.length_singleton] at hmatched; omega
    have ht : I.ts=run.matched+2 := by
      change run.splitCursor [0,15]=_
      simp [TreeRun.splitCursor,TreeRun.consumed,hkey,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm]
    rcases hm with hm|hm
    · simp [nativePrefixEdges,ancestorWalkEdges,terminalWalkEdges,hpath,hseg,hkey,hm,List.range_succ,
        he,hn0,ht,hi,hd,hn,step,withFourWalk,fourWalk,walkEnter1]
    · have hkind := nativePathEdgeKind_terminal hr hfind (show 0<run.matched by omega)
      rw [hdes] at hkind
      simp [nativePrefixEdges,ancestorWalkEdges,terminalWalkEdges,hpath,hseg,hkey,hm,List.range_succ,
        he,hn0,ht,hi,hd,hn,step,withFourWalk,fourWalk,walkEnter1,hkind]
  · have hm : run.matched=0 := by simp only [hkey,List.length_nil] at hmatched; omega
    have ht : I.ts=3 := by
      change run.splitCursor [0,15]=_
      simp [TreeRun.splitCursor,TreeRun.consumed,hkey,hm]
    have hnot : p.kind≠.RDB := by
      intro hk
      have hh := hseg
      simp [partWalkKey,hk] at hh
    have hkind : nativePathEdgeKind run 0=EK_KEY := by
      rw [nativePathEdgeKind_proper hr 0 p hpp,ite_eq_right hnot]
    simp [nativePrefixEdges,ancestorWalkEdges,terminalWalkEdges,hpath,hseg,hkey,hm,List.range_succ,
      he,hn0,ht,hi,hd,hn,step,withFourWalk,fourWalk,walkEnter1,hkind]
end ZkFormal.NearV3.Render.UpsGen
