import ZkFormal.NearV3.Assembly.PathAddress
import ZkFormal.NearV3.Assembly.ViewSegment

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

theorem locatePartChild_view {ns tau n v depth p child}
    (hs : ViewSegment ns tau n v depth p.source)
    (hc : locatePartChild n v depth p=some child) :
    ViewSegment ns tau child.nid child.vid child.depth child.tree := by
  cases ht : p.source <;> simp only [locatePartChild,ht] at hc
  all_goals try contradiction
  · cases hc
    rw [ht] at hs
    exact hs.ext
  · rw [ht] at hs
    exact locateKid_view _ _ _ _ _ _ hs.branch hc

theorem resolveAddress_view {ns tau} : ∀ n v d t,
    ViewSegment ns tau n v d t →
    let a := resolveAddress n v d t
    ViewSegment ns tau a.nid a.vid a.depth a.tree
  | _,_,_,.hash _,h => h
  | _,_,_,.leaf ..,h => h
  | n,v,d,.ext [] c _,h => resolveAddress_view (n+1) v (d+1) c h.ext
  | _,_,_,.ext (_::_) _ _,h => h
  | _,_,_,.branch ..,h => h

private theorem pathTrees_head (ps : List TreePart) (terminal : PTrie) :
    ∃ t, (pathTrees ps terminal).head?=some t := by
  cases ps <;> simp [pathTrees]

/-- Allocate the entire proper source path in the actual record address space.
The source chain is operational (child lookup), not an ID-consistency premise. -/
theorem allocatePath_views {ns tau} (ps : List TreePart) (terminal : PTrie)
    (hc : SourceAddressChain ps terminal) (a : OccurrenceAddress)
    (hs : ViewSegment ns tau a.nid a.vid a.depth a.tree)
    (hh : (pathTrees ps terminal).head?=some a.tree) :
    ∃ addresses, allocatePath a ps=some addresses ∧
      addresses.map OccurrenceAddress.tree=pathTrees ps terminal ∧
      ∀ b ∈ addresses, ViewSegment ns tau b.nid b.vid b.depth b.tree := by
  induction ps generalizing a with
  | nil =>
    have ht : terminal=a.tree := by simpa [pathTrees] using hh
    refine ⟨[a],rfl,by simp [pathTrees,ht],?_⟩
    intro b hb
    simpa using (List.mem_singleton.mp hb ▸ hs)
  | cons p ps ih =>
    have hp : p.source=a.tree := by simpa [pathTrees] using hh
    obtain ⟨next,hn⟩ := pathTrees_head ps terminal
    have hl := hc 0 p (by simp)
    have hl' : (sourcePathChild p).map resolveNative=some next := by
      have hl0 : (sourcePathChild p).map resolveNative=(pathTrees ps terminal)[0]? := by
        simpa only [pathTrees,List.map_cons,List.cons_append,List.getElem?_cons_succ] using hl
      exact hl0.trans (by simpa only [List.head?_eq_getElem?] using hn)
    obtain ⟨child,hchild,hnext⟩ := Option.map_eq_some_iff.mp hl'
    have hloc := locatePartChild_tree a.nid a.vid a.depth p
    rw [hchild,Option.map_eq_some_iff] at hloc
    obtain ⟨c,hloc,hct⟩ := hloc
    have hseg := locatePartChild_view (hp ▸ hs) hloc
    let b := resolveAddress c.nid c.vid c.depth c.tree
    have hb : b.tree=next := by rw [resolveAddress_tree,hct,hnext]
    have htail : SourceAddressChain ps terminal := by
      intro i q hq
      simpa [pathTrees,Nat.add_assoc] using hc (i+1) q (by simpa using hq)
    obtain ⟨addresses,ha,ht,hsall⟩ := ih htail b (resolveAddress_view _ _ _ _ hseg) (by rw [hb]; exact hn)
    refine ⟨a::addresses,?_,?_,?_⟩
    · simp [allocatePath,hloc,ha,b]
    · simp [pathTrees,List.map_cons,ht,hp]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hs
      · exact hsall x hx

/-- Actual native upsert success supplies the operational chain and root. -/
theorem traceUpsert_address_views {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) {ns tau n v depth}
    (hs : ViewSegment ns tau n v depth t) :
    ∃ addresses, allocatePath (resolveAddress n v depth t) (properPath run)=some addresses ∧
      addresses.map OccurrenceAddress.tree=nativePathNodes run ∧
      ∀ b ∈ addresses, ViewSegment ns tau b.nid b.vid b.depth b.tree := by
  apply allocatePath_views (properPath run) run.terminalSource
  · exact traceUpsert_pathChain t key value run hr
  · exact resolveAddress_view _ _ _ _ hs
  · rw [resolveAddress_tree]
    exact traceUpsert_pathHead t key value run hr


/-- Every revealed source in the executable native path names its exact seeded
provider in the global forest, including repeated equal sibling subtrees. -/
theorem forest_traceUpsert_views {ts : List PTrie} {tau : Nat} {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 ts tau=some root) {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree key value=some run) :
    ∃ addresses, allocatePath (resolveAddress root.nid root.vid root.depth root.tree)
        (properPath run)=some addresses ∧
      addresses.map OccurrenceAddress.tree=nativePathNodes run ∧
      ∀ a ∈ addresses, isNode a.tree=true →
        (forestStoreViews ts).nodes[a.nid]?=some (seedNodeView tau a.depth a.nid a.vid a.tree) := by
  have hs := forestRootAt_view (ns:=forestNodes 0 0 0 ts) 0 0 0 ts tau root (by simp) hroot
  obtain ⟨addresses,ha,ht,hall⟩ := traceUpsert_address_views hr hs
  refine ⟨addresses,ha,ht,?_⟩
  intro a hm hn
  simpa only [Nat.zero_add,forestStoreViews] using (hall a hm).get hn

end ZkFormal.NearV3.Assembly
