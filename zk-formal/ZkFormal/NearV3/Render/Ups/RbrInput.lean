import ZkFormal.NearV3.Render.Ups.RbrCopy
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def rbr_sourceLayout (base : UpsPartI) (hk : base.kind=3)
    (old new : NSlot3) (kids : List NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.branch (some old) kids oldMem).wf) :
    SourceLayout (encodePart base (.branch (some old) kids oldMem)
      (.branch (some new) (kids.map snapshotKid) newMem)) := by
  refine ⟨.branch (some old) kids oldMem,hs,rfl,?_⟩
  have hshape : nonemptyFields (nodeRawShape (.branch (some old) kids oldMem)) =
      (encodePart base (.branch (some old) kids oldMem)
        (.branch (some new) (kids.map snapshotKid) newMem)).shape := by
    simp [encodePart,nonempty_node_shape,nodeTypeCode,nodeChildren,NodeGen3.hplenOf,NodeGen3.isLE]
  rw [← hshape]
  change LayoutEdit base.kind _ _
  rw [hk]
  exact LayoutEdit.preserve 3 (by simp) _

def rbr_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=3)
    (old new : NSlot3) (kids : List NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.branch (some old) kids oldMem).wf)
    (hd : (NodeV3.branch (some new) (kids.map snapshotKid) newMem).wf)
    (hlen : new.lenB=(NearSpec.u32 (L I)).map UInt8.toNat)
    (hbytes : ∀ b ∈ (NodeV3.branch (some old) kids oldMem).ser true, b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.branch (some old) kids oldMem)
      (.branch (some new) (kids.map snapshotKid) newMem)) := by
  let Q := encodePart base (.branch (some old) kids oldMem)
    (.branch (some new) (kids.map snapshotKid) newMem)
  let enc := encodePart_encoding base (.branch (some old) kids oldMem)
    (.branch (some new) (kids.map snapshotKid) newMem) hd
  let src := rbr_sourceLayout base hk old new kids oldMem newMem hs
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ?_
    splitBitmap := ?_
    sourceBytes := hbytes
    sourceLayout := fun _ => src
    sourceHeader := ?_
    movedPrefix := ?_
    sourceValue := ?_
    copyFields := rbr_copy I base hk old new kids oldMem newMem hs hd }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · refine ⟨?_⟩
    intro _ _
    exact ⟨new,rfl,hlen⟩
  · refine ⟨hx,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro h; simp [HeaderNeeded,XcpB,Q,encodePart,hk] at h
  · intro h; simp [Q,encodePart,hk] at h
  · intro _ _
    refine ⟨src,?_,rfl,rfl⟩
    change ValueEdit base.kind I.ci (.branch (some old) kids oldMem)
      (.branch (some new) (kids.map snapshotKid) newMem)
    rw [hk]
    exact ValueEdit.branch 3 I.ci (by simp) old new kids (kids.map snapshotKid) oldMem newMem

end ZkFormal.NearV3.Render.UpsGen
