import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupHead

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

mutual
theorem nativeLookupSteps_chain (nid vid : Nat) : ∀tree key steps,
    nativeLookupSteps nid vid tree key=some steps→lookupChain steps
  | .hash _,_,_,h=>by cases h
  | .leaf stored slot mem,key,steps,h=>leafLookupSteps_chain nid vid slot 0 stored key steps h
  | .ext stored child mem,key,steps,h=>by
    cases hp : isPrefix stored key with
    | false=>
      simp only [nativeLookupSteps,hp,Bool.false_eq_true,ite_false] at h
      cases he : leafLookupSteps nid vid (.ref 0 []) 0 stored key with
      | none=>simp [he] at h
      | some raw=>
        simp only [he,Option.map_some,Option.some.injEq] at h;rw [←h]
        exact extensionMismatchFix_chain nid child stored.length raw
          (leafLookupSteps_chain nid vid (.ref 0 []) 0 stored key raw he)
    | true=>
      simp only [nativeLookupSteps,hp,ite_true] at h
      cases ht : nativeLookupSteps (nid+1) vid child (key.drop stored.length) with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h]
        exact lookupExtensionEdges_append_chain nid (viewTarget (nid+1) child) stored tail
          (nativeLookupSteps_chain (nid+1) vid child _ tail ht)
          (fun s hs=>nativeLookupSteps_first (nid+1) vid child _ tail s ht hs)
  | .branch value kids mem,[],steps,h=>by
    cases value with
    | none=>simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h];trivial
    | some v=>cases v with
      | ref l b=>cases h
      | val b=>simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h];trivial
  | .branch value kids mem,x::xs,steps,h=>nativeKidsLookupSteps_chain _ _ _ _ _ _ kids x xs steps h

theorem nativeKidsLookupSteps_chain (parent bm hv sym nid vid : Nat) : ∀kids j key steps,
    nativeKidsLookupSteps parent bm hv sym nid vid kids j key=some steps→lookupChain steps
  | .nil,_,key,steps,h=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h;rw [←h]
    exact lookupDrain_cons_chain _ (by simp) key
  | .none _,0,key,steps,h=>by
    simp only [nativeKidsLookupSteps,Option.some.injEq] at h;rw [←h]
    exact lookupDrain_cons_chain _ (by simp) key
  | .some child _,0,key,steps,h=>by
    simp only [nativeKidsLookupSteps] at h
    cases ht : nativeLookupSteps nid vid child key with
    | none=>simp [ht] at h
    | some tail=>
      simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h]
      apply lookupChain_append [_] tail trivial (nativeLookupSteps_chain nid vid child key tail ht)
      intro a b ha hb
      simp only [List.getLast?_singleton,Option.some.injEq] at ha
      subst a
      have hf:=nativeLookupSteps_first nid vid child key tail b ht hb
      exact lookupNext_matched _ b rfl (by simpa [lookupEdge] using hf.1) hf.2
  | .none rest,j+1,key,steps,h=>nativeKidsLookupSteps_chain parent bm hv sym nid vid rest j key steps h
  | .some child rest,j+1,key,steps,h=>nativeKidsLookupSteps_chain parent bm hv sym
      (nid+tsize child) (vid+(valsOf child).length) rest j key steps h
end

theorem nativeLookupSteps_indexed_chain (nid vid : Nat) (tree : PTrie) (key : List Nat)
    (steps : List WStep3) (h : nativeLookupSteps nid vid tree key=some steps) :
    ∀i (hi : i+1<steps.length),lookupNext steps[i] steps[i+1] :=
  (lookupChain_indexed steps).mp (nativeLookupSteps_chain nid vid tree key steps h)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
