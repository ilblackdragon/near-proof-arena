import ZkFormal.NearV3.Render.Ups.TreeTerminalSources

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows

theorem planned_upper_kind (run : TreeRun) (hp : run.Planned) (k : Nat) (part : TreePart)
    (hk : run.parts[k]?=some part) (hn : (termPlan run.terminal run.matched).length≤k) :
    part.kind.upper=true := by
  obtain ⟨upper,he,hu⟩ := hp
  have hm := congrArg (fun kinds : List UKind => kinds[k]?) he
  simp only [List.getElem?_map,hk,Option.map_some] at hm
  rw [List.getElem?_append] at hm
  simp only [show ¬k<(termPlan run.terminal run.matched).length by omega,ite_false] at hm
  exact hu part.kind (List.mem_of_getElem? hm.symm)

theorem planned_terminal_no_descent (run : TreeRun) (hp : run.Planned) (k : Nat)
    (part : TreePart) (hk : run.parts[k]?=some part)
    (hn : k<(termPlan run.terminal run.matched).length) : descendKind part.kind=false := by
  have hs := remainingDescents_step run.parts k part hk
  rw [planned_terminal_counter run hp k (by omega),planned_terminal_counter run hp (k+1) (by omega)] at hs
  cases hd : descendKind part.kind <;> simp_all

/-- The computed level resolves to the native source for every non-pass-through part.
This is independent of how record IDs are ultimately assigned by the store allocator. -/
theorem allocated_sourceLevel_lookup (recordId : PTrie→Nat) {t : PTrie} {key : List Nat}
    {v : Bytes} {run : TreeRun} (hr : traceUpsert t key v=some run)
    (k : Nat) (part : TreePart) (hk : run.parts[k]?=some part) (Q : UpsPartI)
    (he : Q.kind=part.kind.ix) (hpt : Q.kind≠11) :
    (sourceLevelIds recordId run).getD (withDescentPosition run.parts k Q).sd 0=recordId part.source := by
  have hp := traceUpsert_plan t key v run hr
  by_cases hn : k<(termPlan run.terminal run.matched).length
  · have hd := planned_terminal_no_descent run hp k part hk hn
    have hnot : ¬(Q.kind=0 ∨ Q.kind=1) := by
      cases hc : part.kind <;> simp_all [descendKind,UKind.ix]
    have ht : part∈run.parts.take (termPlan run.terminal run.matched).length := by
      apply List.mem_of_getElem? (i:=k)
      simpa [List.getElem?_take,hn] using hk
    have hs := traceUpsert_terminalSources t key v run hr part ht
    simp only [withDescentPosition,hnot,ite_false,sourceLevelIds_terminal,hs]
  · have hu := planned_upper_kind run hp k part hk (by omega)
    have hd : descendKind part.kind=true := by
      cases hc : part.kind <;> simp_all [UKind.upper,UKind.ix,descendKind]
    have hyes : Q.kind=0 ∨ Q.kind=1 := by
      cases hc : part.kind <;> simp_all [descendKind,UKind.ix]
    simp only [withDescentPosition,hyes,ite_true]
    exact sourceLevelIds_ancestor recordId run k part hk hd
end ZkFormal.NearV3.Render.UpsGen
