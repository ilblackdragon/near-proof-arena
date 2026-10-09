import ZkFormal.NearV3.Assembly.ForestAddress
import ZkFormal.NearV3.Render.Ups.TreeSourceChain

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

theorem locateKid_tree (depth : Nat) : ∀ n v cs i,
    (locateKid depth n v cs i).map OccurrenceAddress.tree=nativeChildAt cs i
  | _,_,.nil,i => by cases i <;> rfl
  | _,_,.none _,0 => rfl
  | _,_,.some _ _,0 => rfl
  | n,v,.none rest,i+1 => locateKid_tree depth n v rest i
  | n,v,.some c rest,i+1 => locateKid_tree depth (n+tsize c) (v+(valsOf c).length) rest i

/-- Address of the actual consumed source child, relative to a located source
occurrence; branch offsets count all preceding node/value occurrences. -/
def locatePartChild (n v depth : Nat) (p : TreePart) : Option OccurrenceAddress :=
  match p.source with
  | .ext _ child _ => some ⟨n+1,v,depth+1,child⟩
  | .branch sv kids _ => locateKid (depth+1) (n+1) (v+(optSlotVal sv).length) kids p.slot
  | _ => none

theorem locatePartChild_tree (n v depth : Nat) (p : TreePart) :
    (locatePartChild n v depth p).map OccurrenceAddress.tree=sourcePathChild p := by
  cases hs : p.source <;> simp [locatePartChild,sourcePathChild,hs,locateKid_tree]

theorem locatePartChild_segment {L VL D tau n v depth p child}
    (hs : Seg L VL D tau n v depth p.source)
    (hc : locatePartChild n v depth p=some child) :
    Seg L VL D tau child.nid child.vid child.depth child.tree := by
  cases ht : p.source <;> simp only [locatePartChild,ht] at hc
  all_goals try contradiction
  · cases hc
    rw [ht] at hs
    exact hs.ext_kid
  · rw [ht] at hs
    exact locateKid_segment _ _ _ _ _ _ hs.br_kids hc

/-- Native adjacent upsert parts have a concrete authenticated child address.
This derives the child provider, rather than assuming an arbitrary recordId map. -/
theorem traceUpsert_child_address {t : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert t key value=some run) {k : Nat} {a b : TreePart}
    (ha : run.parts[k]?=some a) (hb : run.parts[k+1]?=some b) (hu : upperKind b.kind)
    {L VL D tau n v depth} (hs : Seg L VL D tau n v depth b.source) :
    ∃ child, locatePartChild n v depth b=some child ∧ child.tree=a.source ∧
      Seg L VL D tau child.nid child.vid child.depth child.tree := by
  have ht := locatePartChild_tree n v depth b
  rw [traceUpsert_sourceChild hr ha hb hu,Option.map_eq_some_iff] at ht
  obtain ⟨child,hc,he⟩ := ht
  exact ⟨child,hc,he,locatePartChild_segment hs hc⟩

end ZkFormal.NearV3.Assembly
