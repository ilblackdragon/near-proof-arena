import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupChildCursor

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

theorem lookupBranchAbsent_no_edges (nid bm hv sym : Nat) (key : List Nat) :
    ∀s∈lookupBranchAbsent nid bm hv sym key,¬s.mode≤1 := by
  intro s hs hm
  rcases List.mem_cons.mp hs with rfl|hs
  · change 2≤1 at hm;omega
  · exact lookupDrain_no_edges key s hs hm

/-- Branch lookup composes the selected child's exact shifted provider segment. -/
theorem native_branch_edge_coverage (nid vid tau depth : Nat) (value : Option Slot)
    (kids : Kids) (mem : Nat) (key : List Nat) (steps : List WStep3)
    (childCoverage : ∀j child query ss,nativeChildAt kids j=some child→
      nativeLookupSteps (seedChildId (nid+1) kids j)
        (lookupChildVid (vid+(optSlotVal value).length) kids j) child query=some ss→
      ∀s∈ss,s.mode≤1→s.e∈indexedNodeEdges (seedChildId (nid+1) kids j)
        (seedNodesT tau (depth+1) (seedChildId (nid+1) kids j)
          (lookupChildVid (vid+(optSlotVal value).length) kids j) child))
    (h : nativeLookupSteps nid vid (.branch value kids mem) key=some steps) :
    ∀s∈steps,s.mode≤1→s.e∈indexedNodeEdges nid
      (seedNodesT tau depth nid vid (.branch value kids mem)) := by
  intro s hs hm
  cases key with
  | nil=>
    cases value with
    | none=>
      simp only [nativeLookupSteps,Option.some.injEq] at h
      rw [←h] at hs
      simp only [List.mem_singleton] at hs;subst s
      change 2≤1 at hm;omega
    | some slot=>
      cases slot with
      | ref=>cases h
      | val bytes=>
        simp only [nativeLookupSteps,Option.some.injEq] at h
        rw [←h] at hs
        simp only [List.mem_singleton] at hs;subst s
        apply List.mem_append_left
        exact seed_branch_value tau depth nid vid bytes kids mem
  | cons x xs=>
    change nativeKidsLookupSteps nid (kidsBitmap kids 0) (if value.isSome then 1 else 0)
      x (nid+1) (vid+(optSlotVal value).length) kids x xs=some steps at h
    cases hc : nativeChildAt kids x with
    | none=>
      rw [nativeKidsLookupSteps_absent _ _ _ _ _ _ kids x xs hc] at h
      cases h
      exact False.elim (lookupBranchAbsent_no_edges _ _ _ _ _ s hs hm)
    | some child=>
      rw [nativeKidsLookupSteps_selected _ _ _ _ _ _ kids x child xs hc] at h
      cases ht : nativeLookupSteps (seedChildId (nid+1) kids x)
        (lookupChildVid (vid+(optSlotVal value).length) kids x) child xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h
        rw [←h] at hs
        rcases List.mem_cons.mp hs with rfl|hs
        · apply List.mem_append_left
          exact seed_branch_child tau depth nid vid x value kids mem child hc
            (nativeLookupSteps_isNode _ _ _ _ _ ht)
        · apply List.mem_append_right
          exact indexed_child_edges tau (depth+1) (nid+1) (vid+(optSlotVal value).length)
            kids x child hc s.e (childCoverage x child xs tail hc ht s hs hm)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
