import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupForestEdges

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen

def lookupNoBitmap (ss : List WStep3) : Prop := ∀s∈ss,s.mode≠2

private theorem noBitmap_cons (s : WStep3) (ss : List WStep3) (hs : s.mode≠2)
    (ht : lookupNoBitmap ss) : lookupNoBitmap (s::ss) := by
  intro t hm;rcases List.mem_cons.mp hm with rfl|hm
  · exact hs
  · exact ht t hm

private theorem noBitmap_append (a b : List WStep3) (ha : lookupNoBitmap a) (hb : lookupNoBitmap b) :
    lookupNoBitmap (a++b) := by
  intro s hs;rcases List.mem_append.mp hs with hs|hs
  · exact ha s hs
  · exact hb s hs

theorem lookupDrain_no_bitmap (key : List Nat) : lookupNoBitmap (lookupDrain key) := by
  intro s hs
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp hs
  exact (by simp [lookupEdge])

theorem leafLookupSteps_no_bitmap (nid vid : Nat) (slot : Slot) :
    ∀pos stored key steps,leafLookupSteps nid vid slot pos stored key=some steps→lookupNoBitmap steps
  | pos,[],[],steps,h=>by
    cases slot with
    | ref l b=>cases h
    | val b=>simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h];simp [lookupNoBitmap,lookupEdge]
  | pos,a::as,[],steps,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h];simp [lookupNoBitmap,lookupEdge]
  | pos,[],x::xs,steps,h=>by
    simp only [leafLookupSteps,Option.some.injEq] at h;rw [←h]
    exact noBitmap_cons _ _ (by simp [lookupEdge]) (lookupDrain_no_bitmap xs)
  | pos,a::as,x::xs,steps,h=>by
    by_cases he : a=x
    · simp only [leafLookupSteps,he,ite_true] at h
      cases ht : leafLookupSteps nid vid slot (pos+1) as xs with
      | none=>simp [ht] at h
      | some tail=>
        simp only [ht,Option.map_some,Option.some.injEq] at h;rw [←h]
        exact noBitmap_cons _ _ (by simp [lookupEdge]) (leafLookupSteps_no_bitmap nid vid slot (pos+1) as xs tail ht)
    · simp only [leafLookupSteps,he,ite_false,Option.some.injEq] at h;rw [←h]
      exact noBitmap_cons _ _ (by simp [lookupEdge]) (lookupDrain_no_bitmap xs)

theorem extensionMismatchFix_no_bitmap (nid : Nat) (child : PTrie) (len : Nat)
    (ss : List WStep3) (h : lookupNoBitmap ss) : lookupNoBitmap (extensionMismatchFix nid child len ss) := by
  unfold extensionMismatchFix
  split
  · intro s hs
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hs
    simpa only [extensionMismatchStep_mode] using h r hr
  · exact h

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
