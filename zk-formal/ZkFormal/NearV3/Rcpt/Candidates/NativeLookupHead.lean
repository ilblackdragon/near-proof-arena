import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupExtensionChain

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

theorem nativeLookupSteps_isNode (nid vid : Nat) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (h : nativeLookupSteps nid vid tree key=some steps) : isNode tree=true := by
  cases tree with
  | hash b=>cases h
  | leaf=>rfl
  | ext=>rfl
  | branch=>rfl

mutual
theorem nativeLookupSteps_first (nid vid : Nat) : ∀tree key steps s,
    nativeLookupSteps nid vid tree key=some steps→steps.head?=some s→
      s.e.take 2=[viewTarget nid tree,0] ∧ s.mode≤2
  | .hash _,_,_,_,h,_=>by cases h
  | .leaf stored slot mem,key,steps,s,h,hh=>by
    have hf:=leafLookupSteps_first nid vid slot 0 stored key steps s h hh
    exact ⟨hf.1,by omega⟩
  | .ext stored child mem,key,steps,s,h,hh=>by
    cases hp : isPrefix stored key with
    | false=>
      have hs : stored≠[] := by intro hs;subst stored;cases hp
      simp only [nativeLookupSteps,hp,Bool.false_eq_true,ite_false] at h
      cases he : leafLookupSteps nid vid (.ref 0 []) 0 stored key with
      | none=>simp [he] at h
      | some raw=>
        simp only [he,Option.map_some,Option.some.injEq] at h;rw [←h] at hh
        obtain ⟨r,hr,hm,hpair⟩:=extensionMismatchFix_first nid child stored.length raw s hh
        have hf:=leafLookupSteps_first nid vid (.ref 0 []) 0 stored key raw r he hr
        cases stored with
        | nil=>exact False.elim (hs rfl)
        | cons a as=>exact ⟨hpair.trans hf.1,by omega⟩
    | true=>
      simp only [nativeLookupSteps,hp,ite_true] at h
      cases ht : nativeLookupSteps (nid+1) vid child (key.drop stored.length) with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h
        rw [←h] at hh
        cases stored with
        | nil=>
          have hf:=nativeLookupSteps_first (nid+1) vid child _ tail s ht hh
          have hn:=nativeLookupSteps_isNode (nid+1) vid child _ tail ht
          simpa only [viewTarget,hn,ite_true] using hf
        | cons a as=>
          generalize he : lookupExtensionEdges nid (viewTarget (nid+1) child) (a::as)=es at hh
          cases es with
          | nil=>have hz:=congrArg List.length he;simp [lookupExtensionEdges] at hz
          | cons b bs=>
            simp only [List.cons_append,List.head?_cons,Option.some.injEq] at hh
            subst s
            have hf:=lookupExtensionEdges_first_source nid (viewTarget (nid+1) child) (a::as) b
              (by rw [he];rfl)
            exact ⟨hf.2,by omega⟩
  | .branch value kids mem,[],steps,s,h,hh=>by
    cases value with
    | none=>
      simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h] at hh
      simp only [List.head?_cons,Option.some.injEq] at hh;rw [←hh];simp [viewTarget]
    | some v=>cases v with
      | ref l b=>cases h
      | val b=>
        simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h] at hh
        simp only [List.head?_cons,Option.some.injEq] at hh;rw [←hh];simp [viewTarget,lookupEdge]
  | .branch value kids mem,x::xs,steps,s,h,hh=>nativeKidsLookupSteps_first _ _ _ _ _ _ kids x xs steps s h hh

theorem nativeKidsLookupSteps_first (parent bm hv sym nid vid : Nat) : ∀kids j key steps s,
    nativeKidsLookupSteps parent bm hv sym nid vid kids j key=some steps→steps.head?=some s→
      s.e.take 2=[parent,0] ∧ s.mode≤2
  | .nil,_,key,steps,s,h,hh=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h;rw [←h] at hh
    simp only [lookupBranchAbsent,List.head?_cons,Option.some.injEq] at hh;rw [←hh];simp
  | .none _,0,key,steps,s,h,hh=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h;rw [←h] at hh
    simp only [lookupBranchAbsent,List.head?_cons,Option.some.injEq] at hh;rw [←hh];simp
  | .some child _,0,key,steps,s,h,hh=>by
    simp only [nativeKidsLookupSteps] at h
    cases ht : nativeLookupSteps nid vid child key with
    | none=>simp [ht] at h
    | some tail=>
      simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h] at hh
      simp only [List.head?_cons,Option.some.injEq] at hh;rw [←hh];simp [lookupEdge]
  | .none rest,j+1,key,steps,s,h,hh=>nativeKidsLookupSteps_first parent bm hv sym nid vid rest j key steps s h hh
  | .some child rest,j+1,key,steps,s,h,hh=>nativeKidsLookupSteps_first parent bm hv sym
      (nid+tsize child) (vid+(valsOf child).length) rest j key steps s h hh
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
