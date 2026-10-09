import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupProviders

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

theorem leaf_key_provider (nid vid tau depth : Nat) (slot : Slot) (mem : Nat)
    (pre rest : List Nat) (a : Nat) :
    [nid,pre.length,a,nid,pre.length+1,EK_KEY]∈
      edgesOf3 nid (seedNodeView tau depth nid vid (.leaf (pre++a::rest) slot mem)) := by
  have h:=keyEdges3_at_prefix nid pre rest a
  exact List.mem_append_left _ (List.mem_append_left _ h)

theorem leaf_end_provider (nid vid tau depth : Nat) (slot : Slot) (mem : Nat) (key : List Nat) :
    [nid,key.length,SYM_END,nid,key.length,EK_LEND]∈
      edgesOf3 nid (seedNodeView tau depth nid vid (.leaf key slot mem)) := by
  exact List.mem_append_right _ (by simp)

theorem leaf_value_provider (nid vid tau depth : Nat) (value : Bytes) (mem : Nat) (key : List Nat) :
    [nid,key.length,SYM_END,vid,0,EK_VAL]∈
      edgesOf3 nid (seedNodeView tau depth nid vid (.leaf key (.val value) mem)) := by
  change _∈(keyEdges3 nid key++[[nid,key.length,SYM_END,vid,0,EK_VAL]])++_
  exact List.mem_append_left _ (List.mem_append_right _ (by simp))

theorem leafLookupSteps_edge_coverage (nid vid tau depth : Nat) (slot : Slot) (mem : Nat) :
    ∀stored pre key steps,leafLookupSteps nid vid slot pre.length stored key=some steps→
      ∀s∈steps,s.mode≤1→s.e∈
        edgesOf3 nid (seedNodeView tau depth nid vid (.leaf (pre++stored) slot mem))
  | [],pre,[],steps,h,s,hm,hmode=>by
    cases slot with
    | ref l b=>cases h
    | val b=>
      simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h] at hm
      simp only [List.mem_singleton] at hm;subst s
      simpa [lookupEdge] using leaf_value_provider nid vid tau depth b mem pre
  | a::as,pre,[],steps,h,s,hm,hmode=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h] at hm
    simp only [List.mem_singleton] at hm;subst s
    exact leaf_key_provider nid vid tau depth slot mem pre as a
  | [],pre,x::xs,steps,h,s,hm,hmode=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h] at hm
    rcases List.mem_cons.mp hm with rfl|hm
    · simpa [lookupEdge] using leaf_end_provider nid vid tau depth slot mem pre
    · exact False.elim (lookupDrain_no_edges xs s hm hmode)
  | a::as,pre,x::xs,steps,h,s,hm,hmode=>by
    by_cases he : a=x
    · simp only [leafLookupSteps,he,ite_true] at h
      cases ht : leafLookupSteps nid vid slot (pre.length+1) as xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h] at hm
        rcases List.mem_cons.mp hm with rfl|hm
        · simpa [he,lookupEdge] using leaf_key_provider nid vid tau depth slot mem pre as a
        · have ht' : leafLookupSteps nid vid slot (pre++[a]).length as xs=some tail := by simpa using ht
          have hh:=leafLookupSteps_edge_coverage nid vid tau depth slot mem as (pre++[a]) xs tail ht' s hm hmode
          simpa [List.append_assoc] using hh
    · simp only [leafLookupSteps,he,ite_false,Option.some.injEq] at h;rw [←h] at hm
      rcases List.mem_cons.mp hm with rfl|hm
      · exact leaf_key_provider nid vid tau depth slot mem pre as a
      · exact False.elim (lookupDrain_no_edges xs s hm hmode)

theorem native_leaf_edge_coverage (nid vid tau depth : Nat) (slot : Slot) (mem : Nat)
    (stored key : List Nat) (steps : List WStep3)
    (h : nativeLookupSteps nid vid (.leaf stored slot mem) key=some steps) :
    ∀s∈steps,s.mode≤1→s.e∈indexedNodeEdges nid
      (seedNodesT tau depth nid vid (.leaf stored slot mem)) := by
  intro s hs hm
  have hh:=leafLookupSteps_edge_coverage nid vid tau depth slot mem stored [] key steps h s hs hm
  simpa [seedNodesT,indexedNodeEdges] using hh

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
