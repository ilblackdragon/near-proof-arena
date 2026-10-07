import ZkFormal.NearV3.Render.Ups.SourceLevelLookup

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

def sourceDepths (terminalDepth : Nat) (run : TreeRun) : List Nat :=
  ((run.parts.zipIdx.filter (fun p => descendKind p.1.kind)).reverse.map
    (fun p => planDepth terminalDepth (termPlan run.terminal run.matched).length p.2))++[terminalDepth]

private theorem indexed_descent_count (parts : List TreePart) (k : Nat) :
    ((parts.zipIdx.drop k).filter (fun p => descendKind p.1.kind)).length=remainingDescents parts k := by
  have hm : (((parts.zipIdx.drop k).filter (fun p => descendKind p.1.kind)).map Prod.fst)=
      (parts.drop k).filter (fun p => descendKind p.kind) := by
    have he := List.filter_map (f:=Prod.fst) (p:=fun p : TreePart => descendKind p.kind)
      (l:=parts.zipIdx.drop k)
    simpa [Function.comp_def,List.map_drop,List.zipIdx_map_fst] using he.symm
  simpa [remainingDescents,descentCount] using congrArg List.length hm

theorem sourceDepths_length (depth : Nat) (run : TreeRun) :
    (sourceDepths depth run).length=descentCount run.parts+1 := by
  have h := indexed_descent_count run.parts 0
  simpa [sourceDepths,remainingDescents] using h

theorem sourceDepths_terminal (depth : Nat) (run : TreeRun) :
    (sourceDepths depth run).getD (descentCount run.parts) 0=depth := by
  have h := indexed_descent_count run.parts 0
  simp only [List.drop_zero,remainingDescents] at h
  simp [sourceDepths,List.getD_eq_getElem?_getD,List.getElem?_append,h]

theorem sourceDepths_ancestor (depth : Nat) (run : TreeRun) (k : Nat)
    (part : TreePart) (hp : run.parts[k]?=some part) (hd : descendKind part.kind=true) :
    (sourceDepths depth run).getD (remainingDescents run.parts k-1) 0=
      planDepth depth (termPlan run.terminal run.matched).length k := by
  have hs := remainingDescents_step run.parts k part hp
  simp only [hd,ite_true] at hs
  have hb := remainingDescents_le run.parts k
  have hi : remainingDescents run.parts k-1<descentCount run.parts := by omega
  have hz : run.parts.zipIdx[k]?=some (part,k) := by simp [List.getElem?_zipIdx,hp]
  have he := reverse_filter_position (fun p : TreePart×Nat => descendKind p.1.kind)
    (fun p => planDepth depth (termPlan run.terminal run.matched).length p.2) 0
    run.parts.zipIdx k (part,k) hz hd
  rw [indexed_descent_count] at he
  have hlen := indexed_descent_count run.parts 0
  simp only [List.drop_zero,remainingDescents] at hlen
  simpa [sourceDepths,List.getD_eq_getElem?_getD,List.getElem?_append,hlen,hi] using he

/-- Depth and source-level allocation agree on every non-pass-through part. -/
theorem allocated_sourceDepth_lookup {t : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert t key v=some run) (k : Nat) (part : TreePart) (hk : run.parts[k]?=some part)
    (Q : UpsPartI) (he : Q.kind=part.kind.ix) (hpt : Q.kind≠11) (depth : Nat) :
    (sourceDepths depth run).getD (withDescentPosition run.parts k Q).sd 0=
      planDepth depth (termPlan run.terminal run.matched).length k := by
  have hp := traceUpsert_plan t key v run hr
  by_cases hn : k<(termPlan run.terminal run.matched).length
  · have hd := planned_terminal_no_descent run hp k part hk hn
    have hnot : ¬(Q.kind=0 ∨ Q.kind=1) := by
      cases hc : part.kind <;> simp_all [descendKind,UKind.ix]
    simp only [withDescentPosition,hnot,ite_false,sourceDepths_terminal,planDepth_terminal _ _ _ hn]
  · have hu := planned_upper_kind run hp k part hk (by omega)
    have hd : descendKind part.kind=true := by
      cases hc : part.kind <;> simp_all [UKind.upper,UKind.ix,descendKind]
    have hyes : Q.kind=0 ∨ Q.kind=1 := by
      cases hc : part.kind <;> simp_all [descendKind,UKind.ix]
    simp only [withDescentPosition,hyes,ite_true]
    exact sourceDepths_ancestor depth run k part hk hd
end ZkFormal.NearV3.Render.UpsGen
