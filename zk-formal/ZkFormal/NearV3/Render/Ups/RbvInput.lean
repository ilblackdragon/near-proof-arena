import ZkFormal.NearV3.Render.Ups.RbvCopy
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def rbv_sourceLayout (base : UpsPartI) (hk : base.kind=4)
    (new : NSlot3) (kids : List NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.branch none kids oldMem).wf) :
    SourceLayout (encodePart base (.branch none kids oldMem)
      (.branch (some new) (kids.map snapshotKid) newMem)) := by
  refine ⟨.branch none kids oldMem,hs,rfl,?_⟩
  change LayoutEdit base.kind _ _
  rw [hk]
  simp only [encodePart,nonempty_node_shape,nodeTypeCode,nodeChildren,snapshotKids_windows]
  simp only [nodeFields,Nat.reduceLeDiff,ite_false,Nat.reduceEqDiff,or_false,ite_true,
    List.nil_append,List.append_nil,List.cons_append]
  exact LayoutEdit.value _

def rbv_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=4)
    (new : NSlot3) (kids : List NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.branch none kids oldMem).wf)
    (hd : (NodeV3.branch (some new) (kids.map snapshotKid) newMem).wf)
    (hlen : new.lenB=(NearSpec.u32 (L I)).map UInt8.toNat)
    (hbytes : ∀ b ∈ (NodeV3.branch none kids oldMem).ser true, b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.branch none kids oldMem)
      (.branch (some new) (kids.map snapshotKid) newMem)) := by
  let Q := encodePart base (.branch none kids oldMem)
    (.branch (some new) (kids.map snapshotKid) newMem)
  let enc := encodePart_encoding base (.branch none kids oldMem)
    (.branch (some new) (kids.map snapshotKid) newMem) hd
  let src := rbv_sourceLayout base hk new kids oldMem newMem hs
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
    copyFields := rbv_copy I base hk new kids oldMem newMem hs hd }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · refine ⟨?_⟩
    intro _ _
    exact ⟨new,rfl,hlen⟩
  · refine ⟨hx,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro _
    exact ⟨src,rfl,rfl,by simp [Q,encodePart,hk,XcpB],
      by simp [Q,encodePart,hk,XcpB],by intros; rfl⟩
  · intro h; simp [Q,encodePart,hk] at h
  · intro _ h; simp [VcpB,Q,encodePart,hk] at h

end ZkFormal.NearV3.Render.UpsGen
