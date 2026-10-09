import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupBitmapProviders

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

mutual
/-- Every mode-2 request carries the bitmap/value bit of its actual branch provider. -/
theorem nativeLookup_bitmap_coverage (tau depth nid vid : Nat) : ∀tree key steps,
    nativeLookupSteps nid vid tree key=some steps→
    ∀s∈steps,s.mode=2→[s.e.getD 0 0,s.bm,s.hv]∈indexedNodeBitmaps nid (seedNodesT tau depth nid vid tree)
  | .hash _,_,_,h=>by cases h
  | .leaf stored slot mem,key,steps,h=>by
    intro s hs hm
    exact False.elim (leafLookupSteps_no_bitmap nid vid slot 0 stored key steps h s hs hm)
  | .ext stored child mem,key,steps,h=>by
    intro s hs hm
    cases hp : isPrefix stored key with
    | false=>
      simp only [nativeLookupSteps,hp,Bool.false_eq_true,ite_false] at h
      cases hr : leafLookupSteps nid vid (.ref 0 []) 0 stored key with
      | none=>simp [hr] at h
      | some raw=>
        simp only [hr,Option.map_some,Option.some.injEq] at h
        rw [←h] at hs
        exact False.elim (extensionMismatchFix_no_bitmap nid child stored.length raw
          (leafLookupSteps_no_bitmap nid vid (.ref 0 []) 0 stored key raw hr) s hs hm)
    | true=>
      simp only [nativeLookupSteps,hp,ite_true] at h
      cases hc : nativeLookupSteps (nid+1) vid child (key.drop stored.length) with
      | none=>simp [hc] at h
      | some tail=>
        simp only [hc,Option.map_some,Option.some.injEq] at h
        rw [←h] at hs
        rcases List.mem_append.mp hs with hs|hs
        · obtain ⟨j,_,rfl⟩:=List.mem_map.mp hs
          change 0=2 at hm;omega
        · apply List.mem_append_right
          exact nativeLookup_bitmap_coverage tau (depth+1) (nid+1) vid child _ tail hc s hs hm
  | .branch value kids mem,[],steps,h=>by
    intro s hs hm
    cases value with
    | none=>
      simp only [nativeLookupSteps,Option.some.injEq] at h
      rw [←h] at hs
      simp only [List.mem_singleton] at hs;subst s
      apply List.mem_append_left
      exact branch_bitmap_provider tau depth nid vid none kids mem
    | some slot=>
      cases slot with
      | ref=>cases h
      | val bytes=>
        simp only [nativeLookupSteps,Option.some.injEq] at h
        rw [←h] at hs
        simp only [List.mem_singleton] at hs;subst s
        change 0=2 at hm;omega
  | .branch value kids mem,x::xs,steps,h=>by
    intro s hs hm
    change nativeKidsLookupSteps nid (kidsBitmap kids 0) (if value.isSome then 1 else 0)
      x (nid+1) (vid+(optSlotVal value).length) kids x xs=some steps at h
    cases hc : nativeChildAt kids x with
    | none=>
      rw [nativeKidsLookupSteps_absent _ _ _ _ _ _ kids x xs hc] at h
      cases h
      rcases List.mem_cons.mp hs with rfl|hs
      · apply List.mem_append_left
        exact branch_bitmap_provider tau depth nid vid value kids mem
      · exact False.elim (lookupDrain_no_bitmap xs s hs hm)
    | some child=>
      rw [nativeKidsLookupSteps_selected _ _ _ _ _ _ kids x child xs hc] at h
      cases ht : nativeLookupSteps (seedChildId (nid+1) kids x)
        (lookupChildVid (vid+(optSlotVal value).length) kids x) child xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h
        rw [←h] at hs
        rcases List.mem_cons.mp hs with rfl|hs
        · change 0=2 at hm;omega
        · apply List.mem_append_right
          exact indexed_child_bitmaps tau (depth+1) (nid+1) (vid+(optSlotVal value).length)
            kids x child hc _ (nativeKids_selected_bitmap_coverage tau (depth+1) (nid+1)
              (vid+(optSlotVal value).length) kids x child xs tail hc ht s hs hm)

theorem nativeKids_selected_bitmap_coverage (tau depth nid vid : Nat) : ∀kids j child key steps,
    nativeChildAt kids j=some child→
    nativeLookupSteps (seedChildId nid kids j) (lookupChildVid vid kids j) child key=some steps→
    ∀s∈steps,s.mode=2→[s.e.getD 0 0,s.bm,s.hv]∈indexedNodeBitmaps (seedChildId nid kids j)
      (seedNodesT tau depth (seedChildId nid kids j) (lookupChildVid vid kids j) child)
  | .nil,_,_,_,_,h,_=>by simp [nativeChildAt] at h
  | .none _,0,_,_,_,h,_=>by simp [nativeChildAt] at h
  | .some c rest,0,child,key,steps,h,hs=>by
    simp only [nativeChildAt,Option.some.injEq] at h
    subst child
    exact nativeLookup_bitmap_coverage tau depth nid vid c key steps hs
  | .none rest,j+1,child,key,steps,h,hs=>
    nativeKids_selected_bitmap_coverage tau depth nid vid rest j child key steps h hs
  | .some c rest,j+1,child,key,steps,h,hs=>
    nativeKids_selected_bitmap_coverage tau depth (nid+tsize c) (vid+(valsOf c).length)
      rest j child key steps h hs
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
