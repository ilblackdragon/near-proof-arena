import ZkFormal.NearV3.Render.Ups.SpbValueCopy
import ZkFormal.NearV3.Render.Ups.SpbSlots
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def spb_value_input (I : UpsInst) (base : UpsPartI) (hk : base.kind=10) (hi : I.ci=4)
    (key : List Nat) (sv : NSlot3) (child : NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.leaf key sv oldMem).wf)
    (hd : (NodeV3.branch (some (snapshotValue sv)) (splitKids I .none child) newMem).wf)
    (hchild : child≠.none)
    (hbytes : ∀b∈(NodeV3.leaf key sv oldMem).ser true,b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.leaf key sv oldMem)
      (.branch (some (snapshotValue sv)) (splitKids I .none child) newMem)) := by
  let Q := encodePart base (.leaf key sv oldMem)
    (.branch (some (snapshotValue sv)) (splitKids I .none child) newMem)
  let enc := encodePart_encoding base (.leaf key sv oldMem)
    (.branch (some (snapshotValue sv)) (splitKids I .none child) newMem) hd
  let src : SourceLayout Q := {
    node := .leaf key sv oldMem
    wf := hs
    bytes := rfl
    edit := by change LayoutEdit base.kind _ _; rw [hk]; exact LayoutEdit.other 10 (by simp) _ _ }
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ?_
    splitBitmap := splitKids_bitmap I base (.leaf key sv oldMem) (some (snapshotValue sv)) .none child newMem hd hx
      (fun h => False.elim (h hi)) (fun _ => hchild) (fun h => False.elim (h hi))
    sourceBytes := hbytes
    sourceLayout := ?_
    sourceHeader := ?_
    movedPrefix := ?_
    sourceValue := ?_
    copyFields := spb_value_copy I base hk hi key sv (splitKids I .none child) oldMem newMem hs hd }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · refine ⟨?_⟩; intro _ h; simp [VcpB,Q,encodePart,hk,hi] at h
  · intro h; simp [Q,encodePart,hk] at h
  · intro h; simp [HeaderNeeded,XcpB,Q,encodePart,hk,hi] at h
  · intro h; simp [Q,encodePart,hk] at h
  · intro _ _
    refine ⟨src,?_,rfl,rfl⟩
    change ValueEdit base.kind I.ci (.leaf key sv oldMem)
      (.branch (some (snapshotValue sv)) (splitKids I .none child) newMem)
    rw [hk,hi]
    exact ValueEdit.split _ _ _ _ _ _

end ZkFormal.NearV3.Render.UpsGen
