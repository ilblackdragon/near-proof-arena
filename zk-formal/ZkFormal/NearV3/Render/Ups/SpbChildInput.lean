import ZkFormal.NearV3.Render.Ups.SpbChildCopy
import ZkFormal.NearV3.Render.Ups.SpbSlots
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def spb_child_input (I : UpsInst) (base : UpsPartI) (hk : base.kind=10)
    (hi : I.ci=8 ∨ I.ci=10) (key : List Nat) (old new : NKid)
    (sv : Option NSlot3) (oldMem newMem : List Nat) (hn : new≠.none) (hnw : new.wf)
    (hs : (NodeV3.ext key old oldMem).wf)
    (hd : (NodeV3.branch sv (splitKids I (snapshotKid old) new) newMem).wf)
    (hlen : ∀v,sv=some v → v.lenB=(NearSpec.u32 (L I)).map UInt8.toNat)
    (hxy : I.ci=10 → I.x≠splitNewSlot I)
    (hbytes : ∀b∈(NodeV3.ext key old oldMem).ser true,b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.ext key old oldMem)
      (.branch sv (splitKids I (snapshotKid old) new) newMem)) := by
  let Q := encodePart base (.ext key old oldMem)
    (.branch sv (splitKids I (snapshotKid old) new) newMem)
  let enc := encodePart_encoding base (.ext key old oldMem)
    (.branch sv (splitKids I (snapshotKid old) new) newMem) hd
  let src : SourceLayout Q := {
    node := .ext key old oldMem
    wf := hs
    bytes := rfl
    edit := by change LayoutEdit base.kind _ _; rw [hk]; exact LayoutEdit.other 10 (by simp) _ _ }
  have header : SourceHeader I Q src := by
    refine ⟨rfl,rfl,fun _ => rfl,?_,?_⟩
    · intro _; cases sv <;> simp [Q,encodePart,nodeTypeCode,src,NodeGen3.isLeaf]
    · simp [Q,encodePart,hk]
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ?_
    splitBitmap := splitKids_bitmap I base (.ext key old oldMem) sv (snapshotKid old) new newMem hd hx
      (fun _ => by simpa using hs.2.1) (fun _ => hn) ?_
    sourceBytes := hbytes
    sourceLayout := ?_
    sourceHeader := fun _ => ⟨src,header⟩
    movedPrefix := ?_
    sourceValue := ?_
    copyFields := spb_child_copy I base hk hi key old new sv oldMem newMem hn hnw hs hd }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · refine ⟨?_⟩
    intro ht _
    let v := sv.getD default
    have hv : sv=some v := by
      cases hh : sv with
      | none => simp [Q,encodePart,nodeTypeCode,hh] at ht
      | some x => simp [v,hh]
    exact ⟨v,by change sv=some v; exact hv,hlen v hv⟩
  · intro _ hnew
    apply hxy
    rcases hi with hi|hi
    · simp [splitHasNew,hi] at hnew
    · exact hi
  · intro h; simp [Q,encodePart,hk] at h
  · intro h; simp [Q,encodePart,hk] at h
  · intro _ h; apply False.elim
    rcases hi with hi|hi <;> simp [VcpB,Q,encodePart,hk,hi] at h

end ZkFormal.NearV3.Render.UpsGen
