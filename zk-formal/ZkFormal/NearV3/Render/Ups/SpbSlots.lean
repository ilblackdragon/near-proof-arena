import ZkFormal.NearV3.Render.Ups.SplitKids
import ZkFormal.NearV3.Render.Ups.EncodePart

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

theorem splitKids_slots (I : UpsInst) (old new : NKid)
    (hx : I.x<16) (ho : I.ci≠4 → old≠.none) (hn : splitHasNew I → new≠.none)
    (hd : I.ci≠4 → splitHasNew I → I.x≠splitNewSlot I) (j : Nat) (hj : j<16) :
    ((splitKids I old new).getD j .none≠.none ↔
      (I.ci≠4 ∧ j=I.x) ∨ (splitHasNew I ∧ j=splitNewSlot I)) := by
  have hy : splitNewSlot I<16 := by unfold splitNewSlot; split <;> decide
  by_cases h4 : I.ci=4
  · have hnew : splitHasNew I := Or.inl h4
    simp only [splitKids,h4,ite_true]
    rw [oneKid_at _ _ _ hy hj]
    by_cases he : j=splitNewSlot I <;> simp [he,h4,hnew,hn hnew]
  · by_cases hh : splitHasNew I
    · simp only [splitKids,h4,ite_false,hh,ite_true]
      rw [twoEdgeKids_at _ _ _ _ _ hx hj (hd h4 hh)]
      change (if j=I.x then old else if j=splitNewSlot I then new else .none)≠.none ↔ _
      by_cases he : j=I.x <;> by_cases he' : j=splitNewSlot I <;>
        simp [he,he',h4,hh,ho h4,hn hh,Ne.symm (hd h4 hh)]
    · simp only [splitKids,h4,ite_false,hh]
      rw [oneKid_at _ _ _ hx hj]
      by_cases he : j=I.x <;> simp [he,h4,hh,ho h4]

def splitKids_bitmap (I : UpsInst) (base : UpsPartI) (src : NodeV3)
    (sv : Option NSlot3) (old new : NKid) (mem : List Nat)
    (hw : (NodeV3.branch sv (splitKids I old new) mem).wf)
    (hx : I.x<16) (ho : I.ci≠4 → old≠.none) (hn : splitHasNew I → new≠.none)
    (hd : I.ci≠4 → splitHasNew I → I.x≠splitNewSlot I) :
    SplitBitmap I (encodePart base src (.branch sv (splitKids I old new) mem))
      (encodePart_encoding base src (.branch sv (splitKids I old new) mem) hw) := by
  refine ⟨hx,?_,?_⟩
  · intro _ j hj; exact splitKids_slots I old new hx ho hn hd j hj
  · intro _; exact hd

end ZkFormal.NearV3.Render.UpsGen
