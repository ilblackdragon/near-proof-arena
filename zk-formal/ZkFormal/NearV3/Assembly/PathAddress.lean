import ZkFormal.NearV3.Assembly.ResolvedAddress
import ZkFormal.NearV3.Render.Ups.TreePathChain

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

def pathTrees (ps : List TreePart) (terminal : PTrie) : List PTrie :=
  ps.map TreePart.source ++ [terminal]

def SourceAddressChain (ps : List TreePart) (terminal : PTrie) : Prop :=
  ∀ i p, ps[i]?=some p → (sourcePathChild p).map resolveNative=(pathTrees ps terminal)[i+1]?

def allocatePath (a : OccurrenceAddress) : List TreePart → Option (List OccurrenceAddress)
  | [] => some [a]
  | p::ps => do
    let child ← locatePartChild a.nid a.vid a.depth p
    let tail ← allocatePath (resolveAddress child.nid child.vid child.depth child.tree) ps
    pure (a::tail)

private theorem pathTrees_head (ps : List TreePart) (terminal : PTrie) :
    ∃ t, (pathTrees ps terminal).head?=some t := by
  cases ps <;> simp [pathTrees]

/-- Allocate the entire proper source path in the actual record address space.
The source chain is operational (child lookup), not an ID-consistency premise. -/
theorem allocatePath_complete {L VL D tau} (ps : List TreePart) (terminal : PTrie)
    (hc : SourceAddressChain ps terminal) (a : OccurrenceAddress)
    (hs : Seg L VL D tau a.nid a.vid a.depth a.tree)
    (hh : (pathTrees ps terminal).head?=some a.tree) :
    ∃ addresses, allocatePath a ps=some addresses ∧
      addresses.map OccurrenceAddress.tree=pathTrees ps terminal ∧
      ∀ b ∈ addresses, Seg L VL D tau b.nid b.vid b.depth b.tree := by
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
    have hseg := locatePartChild_segment (hp ▸ hs) hloc
    let b := resolveAddress c.nid c.vid c.depth c.tree
    have hb : b.tree=next := by rw [resolveAddress_tree,hct,hnext]
    have htail : SourceAddressChain ps terminal := by
      intro i q hq
      simpa [pathTrees,Nat.add_assoc] using hc (i+1) q (by simpa using hq)
    obtain ⟨addresses,ha,ht,hsall⟩ := ih htail b (resolveAddress_segment _ _ _ _ hseg) (by rw [hb]; exact hn)
    refine ⟨a::addresses,?_,?_,?_⟩
    · simp [allocatePath,hloc,ha,b]
    · simp [pathTrees,List.map_cons,ht,hp]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hs
      · exact hsall x hx

/-- Actual native upsert success supplies the operational chain and root. -/
theorem traceUpsert_addresses {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) {L VL D tau n v depth}
    (hs : Seg L VL D tau n v depth t) :
    ∃ addresses, allocatePath (resolveAddress n v depth t) (properPath run)=some addresses ∧
      addresses.map OccurrenceAddress.tree=nativePathNodes run ∧
      ∀ b ∈ addresses, Seg L VL D tau b.nid b.vid b.depth b.tree := by
  apply allocatePath_complete (properPath run) run.terminalSource
  · exact traceUpsert_pathChain t key value run hr
  · exact resolveAddress_segment _ _ _ _ hs
  · rw [resolveAddress_tree]
    exact traceUpsert_pathHead t key value run hr

end ZkFormal.NearV3.Assembly
