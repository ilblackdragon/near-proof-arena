import ZkFormal.NearV3.Render.Ups.NativeBranchProvider

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

theorem nativePathNode_valueView (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat)
    (source : PTrie) (view : NodeV3)
    (hv : nativePathNode recordId resolvedId valueId source=some view) :
    NativeValueView valueId source view := by
  cases source with
  | hash => simp [nativePathNode,nativeKeyNode] at hv
  | ext => trivial
  | leaf key slot mem =>
    cases slot with
    | ref => trivial
    | val bytes =>
      simp only [nativePathNode,nativeKeyNode,Option.some.injEq] at hv
      subst view
      exact ⟨_,_,_,_,_,_,rfl⟩
  | branch value kids mem =>
    cases value with
    | none => trivial
    | some slot =>
      cases slot with
      | ref => trivial
      | val bytes =>
        simp only [nativePathNode,Option.some.injEq] at hv
        subst view
        exact ⟨_,_,_,_,_,_,_,rfl⟩

theorem nativePathNode_key_eq (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat)
    {root : PTrie} {v : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] v=some run)
    (hc : 4≤run.terminal.ix) :
    nativePathNode recordId resolvedId valueId run.terminalSource=
      nativeKeyNode recordId resolvedId valueId run.terminalSource := by
  have hk := traceUpsert_keyTerminal root [0,15] v run hr
  cases hcs : run.terminal <;> simp only [hcs,UCase.ix] at hc
  all_goals try omega
  all_goals simp only [KeyTerminal,hcs] at hk
  all_goals obtain ⟨key,slot,mem,hs,_⟩ := hk
  all_goals rw [hs]; rfl

/-- Every generated terminal lookup is supplied by the corresponding executable native
source annotation: value/key EDGE or absent-branch BMAP. Source serialization is unchanged.
Only ordinary read determinacy and the allocator's record/value maps are inputs. -/
theorem nativePathNode_terminalProvider (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat)
    (baseI : UpsInst) {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hfind : root.find [0,15]≠none)
    (Qs : List UpsPartI) (s : NodeS3)
    (hnode : nativePathNode recordId resolvedId valueId run.terminalSource=some s.v) :
    let I := nativeInstance recordId (nativeWalkBase recordId valueId resolvedId baseI root run v)
      root run v Qs
    ((run.terminal=.BV ∨ run.terminal=.BI) ∧
      s.v.bmap=some ((step I I.ts).bm,(step I I.ts).hv)) ∨
      (step I I.ts).e∈edgesOf3 (recordId run.terminalSource) s := by
  dsimp only
  by_cases hbr : run.terminal=.BV ∨ run.terminal=.BI
  · exact Or.inl ⟨hbr,nativeInstance_branch_bitmap recordId valueId resolvedId baseI hr hbr Qs s hnode⟩
  right
  by_cases hval : run.terminal=.LP ∨ run.terminal=.BR
  · exact nativeInstance_value_edge recordId valueId resolvedId baseI hr hfind hval Qs s
      (nativePathNode_valueView recordId resolvedId valueId run.terminalSource s.v hnode)
  · have hc : 4≤run.terminal.ix := by cases h : run.terminal <;> simp_all [UCase.ix]
    apply nativeInstance_key_edge recordId valueId resolvedId baseI hr hc Qs s
    rw [←nativePathNode_key_eq recordId resolvedId valueId hr hc]
    exact hnode
end ZkFormal.NearV3.Render.UpsGen
