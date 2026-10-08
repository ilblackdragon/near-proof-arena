import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupFinalTools

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

theorem branchAbsent_final (nid bm hv sym : Nat) (key : List Nat) :
    (lookupBranchAbsent nid bm hv sym key).getLast?.map lookupFinal=some none := by
  change ([(⟨2,sym,[nid,0,0,0,0,0],0,bm,hv,0⟩ : WStep3)]++lookupDrain key).getLast?.map lookupFinal=some none
  rw [List.getLast?_append,lookupDrain_last]
  rfl

mutual
/-- The terminal VID is the exact ordinal in the existing revealed-value allocator. -/
theorem nativeLookup_valueIndex (nid vid : Nat) : ∀tree key ss,
    nativeLookupSteps nid vid tree key=some ss→
    ss.getLast?.map lookupFinal=some ((valueIndex tree key).map (vid+·))
  | .hash _,_,_,h=>by cases h
  | .leaf stored slot mem,key,ss,h=>leaf_lookup_valueIndex nid vid slot mem stored key ss h
  | .ext stored child mem,key,ss,h=>by
    cases hp : isPrefix stored key with
    | false=>
      simp only [nativeLookupSteps,hp,Bool.false_eq_true,ite_false] at h
      cases hr : leafLookupSteps nid vid (.ref 0 []) 0 stored key with
      | none=>simp [hr] at h
      | some raw=>
        simp only [hr,Option.map_some,Option.some.injEq] at h
        rw [←h,extensionMismatchFix_final,leaf_lookup_valueIndex nid vid (.ref 0 []) mem stored key raw hr]
        simp [valueIndex,slotValueIndex,hp]
    | true=>
      simp only [nativeLookupSteps,hp,ite_true] at h
      cases hc : nativeLookupSteps (nid+1) vid child (key.drop stored.length) with
      | none=>simp [hc] at h
      | some tail=>
        simp only [hc,Option.map_some,Option.some.injEq] at h
        rw [←h,lookup_append_final _ tail (native_lookup_nonempty _ _ _ _ _ hc),
          nativeLookup_valueIndex (nid+1) vid child _ tail hc]
        simp only [valueIndex,hp,ite_true]
  | .branch value kids mem,[],ss,h=>by
    cases value with
    | none=>simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h];rfl
    | some slot=>cases slot with
      | ref=>cases h
      | val b=>simp only [nativeLookupSteps,Option.some.injEq] at h;rw [←h];simp [valueIndex,optSlotValueIndex,slotValueIndex,lookupFinal,lookupEdge]
  | .branch value kids mem,x::xs,ss,h=>by
    have hh:=nativeKidsLookup_valueIndex nid (kidsBitmap kids 0) (if value.isSome then 1 else 0)
      x (nid+1) (vid+(optSlotVal value).length) kids x xs ss h
    rw [hh]
    simp only [valueIndex,Option.map_map,Function.comp_def,Nat.add_assoc]
    rfl

theorem nativeKidsLookup_valueIndex (parent bm hv sym nid vid : Nat) : ∀kids j key ss,
    nativeKidsLookupSteps parent bm hv sym nid vid kids j key=some ss→
    ss.getLast?.map lookupFinal=some ((kidValueIndex kids j key).map (vid+·))
  | .nil,_,key,ss,h=>by cases h;exact branchAbsent_final _ _ _ _ key
  | .none _,0,key,ss,h=>by cases h;exact branchAbsent_final _ _ _ _ key
  | .some child rest,0,key,ss,h=>by
    simp only [nativeKidsLookupSteps] at h
    cases hc : nativeLookupSteps nid vid child key with
    | none=>simp [hc] at h
    | some tail=>
      simp only [hc,Option.map_some,Option.some.injEq] at h
      rw [←h]
      change ([lookupEdge 0 sym [parent,0,sym,viewTarget nid child,0,EK_DOWN]]++tail).getLast?.map lookupFinal=_
      rw [lookup_append_final _ tail (native_lookup_nonempty _ _ _ _ _ hc)]
      exact nativeLookup_valueIndex nid vid child key tail hc
  | .none rest,j+1,key,ss,h=>nativeKidsLookup_valueIndex parent bm hv sym nid vid rest j key ss h
  | .some child rest,j+1,key,ss,h=>by
    rw [nativeKidsLookup_valueIndex parent bm hv sym (nid+tsize child)
      (vid+(valsOf child).length) rest j key ss h]
    simp only [kidValueIndex,Option.map_map,Function.comp_def,native_valsOf_eq,Nat.add_assoc]
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
