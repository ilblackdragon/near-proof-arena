import ZkFormal.NearV3.Render.Ups.ReverseFilterPosition

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

/-- Source levels in top-down walk order, skipping empty-extension pass-throughs.
The record lookup remains supplied by the store allocator. -/
def sourceLevelIds (recordId : PTrie→Nat) (run : TreeRun) : List Nat :=
  ((run.parts.filter (fun p => descendKind p.kind)).reverse.map (fun p => recordId p.source))++
    [recordId run.terminalSource]

theorem sourceLevelIds_length (recordId : PTrie→Nat) (run : TreeRun) :
    (sourceLevelIds recordId run).length=descentCount run.parts+1 := by
  simp [sourceLevelIds,descentCount]

theorem sourceLevelIds_terminal (recordId : PTrie→Nat) (run : TreeRun) :
    (sourceLevelIds recordId run).getD (descentCount run.parts) 0=recordId run.terminalSource := by
  simp [sourceLevelIds,descentCount,List.getD_eq_getElem?_getD,List.getElem?_append]

/-- A proper ancestor reads precisely the source record at its computed source level. -/
theorem sourceLevelIds_ancestor (recordId : PTrie→Nat) (run : TreeRun) (k : Nat)
    (part : TreePart) (hp : run.parts[k]?=some part) (hd : descendKind part.kind=true) :
    (sourceLevelIds recordId run).getD (remainingDescents run.parts k-1) 0=recordId part.source := by
  have hs := remainingDescents_step run.parts k part hp
  simp only [hd,ite_true] at hs
  have hb := remainingDescents_le run.parts k
  have hi : remainingDescents run.parts k-1<descentCount run.parts := by omega
  have he := reverse_filter_position (fun p : TreePart => descendKind p.kind)
    (fun p => recordId p.source) 0 run.parts k part hp hd
  simpa [sourceLevelIds,remainingDescents,descentCount,List.getD_eq_getElem?_getD,
    List.getElem?_append,show ((run.parts.drop k).filter (fun p => descendKind p.kind)).length-1<
      (run.parts.filter (fun p => descendKind p.kind)).length from hi] using he

/-- A native fixed-key trace has at most three source records, regardless of revealed depth. -/
theorem sourceLevelIds_capacity (recordId : PTrie→Nat) {t : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t [0,15] v=some run) : (sourceLevelIds recordId run).length≤3 := by
  rw [sourceLevelIds_length]
  have h := fixed_trace_descents hr
  omega
end ZkFormal.NearV3.Render.UpsGen
