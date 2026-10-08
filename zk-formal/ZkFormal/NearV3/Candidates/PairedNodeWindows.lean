import ZkFormal.NearV3.Rcpt.Candidates.NodePairedWf
import ZkFormal.NearV3.Candidates.NativeNodeChildIds

namespace ZkFormal.NearV3.Candidates.PairedNodeWindows
open NearSpec ZkFormal.Near Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem kid_ids (n : Nat) (a b : PTrie) :
    kidIds (pairedKid n a b)=kidIds (viewKid n a) := by
  unfold pairedKid viewKid
  split <;> rfl

theorem kids_ids : ∀(n : Nat){a b : Kids},WriteKidsPair a b →
    (pairedKids n a b).flatMap kidIds=(viewKids n a).flatMap kidIds
  | _,_,_,.nil => rfl
  | n,_,_,.none h => by simpa [pairedKids,viewKids,kidIds] using kids_ids n h
  | n,_,_,.some h hs => by
    simp only [pairedKids,viewKids,List.flatMap_cons,kid_ids]
    rw [kids_ids _ hs]

/-- Actual post digests do not change preallocated child-window identifiers. -/
theorem node_ids (n v : Nat) {a b : PTrie} (h : WriteTreePair a b) :
    windowIds (pairedNode n v a b)=windowIds (viewNode n v a) := by
  cases h with
  | hash hh => rfl
  | leaf k m hs =>
    change List.replicate ((pairedNode n v (.leaf k _ m) (.leaf k _ m)).ser false).length 0 = _
    rw [pairedNode_pre n v (.leaf k m hs)]
    rfl
  | ext k m hc => simp only [pairedNode,viewNode,windowIds,kid_ids]
  | branch m hv hcs =>
    cases hv with
    | none => simp only [pairedNode,viewNode,windowIds,Option.map_none,kids_ids _ hcs]
    | some hs => simp only [pairedNode,viewNode,windowIds,Option.map_some,Option.isSome_some,kids_ids _ hcs]

/-- The preserved IDs equal the paired renderer's physical child-ID column. -/
theorem physical_ids (n v : Nat) {a b : PTrie} (h : WriteTreePair a b)
    (hw : (viewNode n v a).wf) (p : Nat) :
    (windowIds (viewNode n v a)).getD p 0=
      NativeNodeChildIds.cid
        ((ZkFormal.Near.Render.NodeGen.layout (Render.NodeGen3.fieldsOf (pairedNode n v a b))
          (Render.NodeGen3.hplenOf (pairedNode n v a b))).getD p default).1 := by
  rw [←node_ids n v h]
  exact NativeNodeChildIds.window_at _ (pairedNode_wf n v h hw) p

end ZkFormal.NearV3.Candidates.PairedNodeWindows
