import ZkFormal.NearV3.Render.Ups.NativePrefixOne

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

private theorem two_nonempty_append_two (xs ys zs : List Nat) (hx : xs≠[]) (hy : ys≠[])
    (he : xs++ys++zs=[0,15]) : xs=[0] ∧ ys=[15] ∧ zs=[] := by
  have hl := congrArg List.length he
  have hxl : 0<xs.length := List.length_pos_iff.mpr hx
  have hyl : 0<ys.length := List.length_pos_iff.mpr hy
  simp only [List.length_append,List.length_cons,List.length_nil] at hl
  obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp (show xs.length=1 by omega)
  obtain ⟨b,rfl⟩ := List.length_eq_one_iff.mp (show ys.length=1 by omega)
  have hz : zs=[] := List.eq_nil_of_length_eq_zero (by simp only [List.length_singleton] at hl; omega)
  subst zs
  simpa using he

/-- Both proper ancestors consume one nibble: physical W1/W2 are exactly those edges. -/
theorem nativePrefixEdges_two (recordId : PTrie→Nat) (valueId : Slot→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (p q : TreePart) (hpath : properPath run=[p,q]) (Qs : List UpsPartI) :
    nativePrefixEdges recordId run=nativePhysicalPrefixEdges recordId valueId baseI root run v Qs := by
  let I := nativeInstance recordId baseI root run v Qs
  let target := nativeTerminalTarget valueId (resolvedRecordId recordId) run (recordId run.terminalSource)
  change nativePrefixEdges recordId run=(List.range (I.ts-1)).map fun i =>
    (step (withFourWalk I (terminalBitmap run) (terminalHasVal run)
      (nativePathEdgeKind run 0) (nativePathEdgeKind run (if walkEnter1 I then 1 else 0)) target.1 target.2) (i+1)).e
  have hpp : (properPath run)[0]?=some p := by simp [hpath]
  have hqq : (properPath run)[1]?=some q := by simp [hpath]
  have hpm := properPath_mem hpp
  have hqm := properPath_mem hqq
  have hpn := properSource_walkKey_nonempty (traceUpsert_properSources root [0,15] v run hr p hpm.1) hpm.2
  have hqn := properSource_walkKey_nonempty (traceUpsert_properSources root [0,15] v run hr q hqm.1) hqm.2
  have hquery : partWalkKey p++partWalkKey q++run.terminalKey=[0,15] := by
    have hquery := traceUpsert_walkQuery root [0,15] v run hr
    change (properPath run).flatMap partWalkKey++run.terminalKey=[0,15] at hquery
    simpa [hpath,List.append_assoc] using hquery
  obtain ⟨hpkey,hqkey,hkey⟩ := two_nonempty_append_two _ _ _ hpn hqn hquery
  obtain ⟨_,_,_,hmatched⟩ := traceUpsert_keys root [0,15] v run hr
  have hm : run.matched=0 := by simp only [hkey,List.length_nil] at hmatched; omega
  have hn0 : sourceLevelIds recordId run=[recordId p.source,recordId q.source,recordId run.terminalSource] := by
    change (properPath run).map (fun p => recordId p.source)++[recordId run.terminalSource]=_
    rw [hpath]; rfl
  have hn : I.N=[recordId p.source,recordId q.source,recordId run.terminalSource] := hn0
  have hd : I.D=2 := by
    change descentCount run.parts=2
    have hh := congrArg List.length hpath
    simpa only [properPath,descentCount,List.length_reverse,List.length_cons,List.length_nil] using hh
  have hi : I.ti=0 := hm
  have ht : I.ts=3 := by
    change run.splitCursor [0,15]=_
    simp [TreeRun.splitCursor,TreeRun.consumed,hkey,hm]
  have he0 := fun i => partWalkEdge_sourceLevels recordId hr 0 p hpp i
  have he1 := fun i => partWalkEdge_sourceLevels recordId hr 1 q hqq i
  simp [nativePrefixEdges,ancestorWalkEdges,terminalWalkEdges,hpath,hpkey,hqkey,hkey,hm,List.range_succ,
    he0,he1,hn0,ht,hi,hd,hn,step,withFourWalk,fourWalk,walkEnter1]

/-- The complete physical pre-terminal walk equals the actual native edge sequence.
The proof uses only a successful native run and an ordinary determinate query. -/
theorem nativePrefixEdges_physical (recordId : PTrie→Nat) (valueId : Slot→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hfind : root.find [0,15]≠none) (Qs : List UpsPartI) :
    nativePrefixEdges recordId run=nativePhysicalPrefixEdges recordId valueId baseI root run v Qs := by
  have hd : (properPath run).length≤2 := by
    have hh := fixed_trace_descents hr
    simpa only [properPath,descentCount,List.length_reverse] using (show descentCount run.parts≤2 by omega)
  cases hp : properPath run with
  | nil => exact nativePrefixEdges_zero recordId valueId baseI hr hfind hp Qs
  | cons p rest =>
    cases rest with
    | nil => exact nativePrefixEdges_one recordId valueId baseI hr hfind p hp Qs
    | cons q rest =>
      have hz : rest=[] := by
        rw [hp] at hd
        exact List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hd; omega)
      subst rest
      exact nativePrefixEdges_two recordId valueId baseI hr p q hp Qs
end ZkFormal.NearV3.Render.UpsGen
