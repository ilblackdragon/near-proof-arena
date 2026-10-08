import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupStartCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

structure NativeLookupQuery where
  wid : Nat
  tau : Nat
  key : List Nat

/-- Fail on an unavailable transition or an unresolved lookup; no query is dropped. -/
def nativeQueryWalk (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery) : Option WalkR := do
  let (tree,_) ← pairs[q.tau]?
  let before := (pairs.take q.tau).map Prod.fst
  let steps ← nativeLookupSteps (forestLookupNid before) (forestLookupVid before) tree q.key
  pure (nativeLookupWalk q.wid q.tau (forestLookupNid before) tree steps)

theorem nativeQueryWalk_coverage (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery)
    (w : WalkR) (h : nativeQueryWalk pairs q=some w) :
    (∀s∈w.steps,s.mode≤1→s.e∈headEdgeKeys (forestWalkHeads 0 0 pairs)++
      nodeEdgeKeys (forestStoreViews (pairs.map Prod.fst)).nodes) ∧
    (∀s∈w.steps,s.mode=2→[s.e.getD 0 0,s.bm,s.hv]∈
      nodeBitmapKeys (forestStoreViews (pairs.map Prod.fst)).nodes) := by
  cases hp : pairs[q.tau]? with
  | none=>simp [nativeQueryWalk,hp] at h
  | some pair=>
    obtain ⟨tree,post⟩:=pair
    have hi : q.tau<pairs.length := (List.getElem?_eq_some_iff.mp hp).1
    have hsplit : pairs=pairs.take q.tau++(tree,post)::pairs.drop (q.tau+1) := by
      have hd:=List.drop_eq_getElem_cons hi
      rw [(List.getElem?_eq_some_iff.mp hp).2] at hd
      simpa only [hd] using (List.take_append_drop q.tau pairs).symm
    dsimp only [nativeQueryWalk] at h
    rw [hp] at h
    dsimp only [Bind.bind,Option.bind] at h
    cases hs : nativeLookupSteps (forestLookupNid ((pairs.take q.tau).map Prod.fst))
      (forestLookupVid ((pairs.take q.tau).map Prod.fst)) tree q.key with
    | none=>rw [hs] at h;cases h
    | some steps=>
      rw [hs] at h
      have h := Option.some.inj h
      subst w
      have he:=native_forest_walk_edges (pairs.take q.tau) (pairs.drop (q.tau+1)) tree post q.wid q.key steps hs
      have hb:=native_forest_walk_bitmaps (pairs.take q.tau) (pairs.drop (q.tau+1)) tree post q.wid q.key steps hs
      rw [←hsplit] at he hb
      simpa only [List.length_take,Nat.min_eq_left (Nat.le_of_lt hi)] using And.intro he hb

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
