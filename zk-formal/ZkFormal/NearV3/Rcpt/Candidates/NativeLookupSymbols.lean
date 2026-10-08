import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupTree

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

theorem lookupExtensionEdges_symbols (nid target : Nat) (key : List Nat) :
    (lookupExtensionEdges nid target key).map WStep3.sym=key := by
  simp only [lookupExtensionEdges,List.map_map,Function.comp_def,lookupEdge]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]

private theorem prefix_drop : ∀stored key : List Nat,isPrefix stored key=true→
    stored++key.drop stored.length=key
  | [],key,_=>rfl
  | _::_,[],h=>by cases h
  | a::as,x::xs,h=>by
    simp only [isPrefix,Bool.and_eq_true,beq_iff_eq] at h
    simp [h.1,prefix_drop as xs h.2]

mutual
theorem nativeLookupSteps_symbols (nid vid : Nat) : ∀tree key steps,
    nativeLookupSteps nid vid tree key=some steps→steps.map WStep3.sym=key++[SYM_END]
  | .hash _,_,_,h=>by cases h
  | .leaf stored slot _,key,steps,h=>leafLookupSteps_symbols nid vid slot 0 stored key steps h
  | .ext stored child mem,key,steps,h=>by
    cases hp : isPrefix stored key with
    | false=>
      simp only [nativeLookupSteps,hp,Bool.false_eq_true,ite_false] at h
      exact leafLookupSteps_symbols nid vid (.ref 0 []) 0 stored key steps h
    | true=>
      simp only [nativeLookupSteps,hp,ite_true] at h
      cases hc : nativeLookupSteps (nid+1) vid child (key.drop stored.length) with
      | none=>simp [hc] at h
      | some tail=>
        simp only [hc,Option.map_some,Option.some.injEq] at h
        rw [←h,List.map_append,lookupExtensionEdges_symbols,
          nativeLookupSteps_symbols (nid+1) vid child _ tail hc,←List.append_assoc,prefix_drop stored key hp]
  | .branch value kids mem,[],steps,h=>by
    cases value with
    | none=>simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h];rfl
    | some v=>cases v with
      | ref l b=>cases h
      | val b=>simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h];rfl
  | .branch value kids mem,x::xs,steps,h=>
    nativeKidsLookupSteps_symbols _ _ _ x _ _ kids x xs steps h

theorem nativeKidsLookupSteps_symbols (parent bm hv sym nid vid : Nat) : ∀kids j key steps,
    nativeKidsLookupSteps parent bm hv sym nid vid kids j key=some steps→
      steps.map WStep3.sym=sym::(key++[SYM_END])
  | .nil,_,key,steps,h=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h
    rw [←h];simp [lookupBranchAbsent,lookupDrain_symbols]
  | .none _,0,key,steps,h=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h
    rw [←h];simp [lookupBranchAbsent,lookupDrain_symbols]
  | .some child _,0,key,steps,h=>by
    simp only [nativeKidsLookupSteps] at h
    cases hc : nativeLookupSteps nid vid child key with
    | none=>simp [hc] at h
    | some tail=>
      simp only [hc,Option.map_some,Option.some.injEq] at h
      rw [←h]
      simp only [List.map_cons,lookupEdge,nativeLookupSteps_symbols nid vid child key tail hc]
  | .none rest,j+1,key,steps,h=>nativeKidsLookupSteps_symbols parent bm hv sym nid vid rest j key steps h
  | .some child rest,j+1,key,steps,h=>nativeKidsLookupSteps_symbols parent bm hv sym
      (nid+tsize child) (vid+(valsOf child).length) rest j key steps h
end

theorem nativeLookupSteps_length (nid vid : Nat) (tree : PTrie) (key : List Nat) (steps : List WStep3)
    (h : nativeLookupSteps nid vid tree key=some steps) : steps.length=key.length+1 := by
  have hh:=congrArg List.length (nativeLookupSteps_symbols nid vid tree key steps h)
  simpa using hh

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
