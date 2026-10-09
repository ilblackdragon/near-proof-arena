import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupJointInventory

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

/-- START requests depend on the prestate root target, not the scheduler or
final execution post digest. This does not equate the complete HEAD records. -/
theorem forest_head_keys_prestate (a b : List (PTrie×PTrie))
    (h : a.map Prod.fst=b.map Prod.fst) (tau nid : Nat) :
    headEdgeKeys (forestWalkHeads tau nid a)=headEdgeKeys (forestWalkHeads tau nid b) := by
  induction a generalizing b tau nid with
  | nil=>cases b <;> simp_all [headEdgeKeys,forestWalkHeads]
  | cons x xs ih=>
    cases b with
    | nil=>simp at h
    | cons y ys=>
      simp only [List.map_cons,List.cons.injEq] at h
      obtain ⟨xp,xpost⟩:=x
      obtain ⟨yp,ypost⟩:=y
      dsimp only at h
      obtain ⟨rfl,ht⟩:=h
      simp only [headEdgeKeys,forestWalkHeads,List.map_cons]
      congr 1
      exact ih ys ht _ _

/-- Transfer the complete shared provider inventory across identical ordered
prestate occurrences while retaining potentially different poststate digests. -/
theorem native_query_ups_prestate_coverage (pairs upsPairs : List (PTrie×PTrie))
    (hp : upsPairs.map Prod.fst=pairs.map Prod.fst) (qs : List NativeLookupQuery)
    (ws : List WalkR) (Is : List Render.UpsInst) (hq : nativeQueryWalks pairs qs=some ws)
    (hu : ∀I∈Is,∃run,InstOk I ∧ DispatchNativeWalkProviders upsPairs run I ∧ I.ci=run.terminal.ix) :
    (∀e∈walkEdgeKeys (ws++upsWalkInventory Is),e∈headEdgeKeys (forestWalkHeads 0 0 pairs)++
      nodeEdgeKeys (forestStoreViews (pairs.map Prod.fst)).nodes) ∧
    (∀e∈walkBmapKeys (ws++upsWalkInventory Is),e∈nodeBitmapKeys (forestStoreViews (pairs.map Prod.fst)).nodes) := by
  have hqc:=nativeQueryWalks_coverage pairs qs ws hq
  have hue:=ups_edge_inventory_coverage upsPairs Is (by
    intro I hI
    obtain ⟨run,ho,hh,hi⟩:=hu I hI
    exact ⟨run,ho,dispatchProviders_forget hh,hi⟩)
  have hub:=ups_bitmap_inventory_coverage upsPairs Is hu
  rw [hp,forest_head_keys_prestate upsPairs pairs hp 0 0] at hue
  rw [hp] at hub
  constructor
  · intro e he
    simp only [walkEdgeKeys,List.flatMap_append,List.filterMap_append,List.mem_append] at he
    exact he.elim (hqc.1 e) (hue e)
  · intro e he
    simp only [walkBmapKeys,List.flatMap_append,List.filterMap_append,List.mem_append] at he
    exact he.elim (hqc.2 e) (hub e)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
