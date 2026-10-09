import ZkFormal.NearV3.Render.Ups.RdbCopy
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def rdb_sourceLayout (base : UpsPartI) (hk : base.kind=0)
    (sv : Option NSlot3) (rest : List NKid) (old new : NKid) (oldMem newMem : List Nat)
    (ho : old≠.none) (hn : new≠.none)
    (hs : (NodeV3.branch sv (edgeKids base.sd old rest) oldMem).wf) :
    SourceLayout (encodePart base (.branch sv (edgeKids base.sd old rest) oldMem)
      (.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem)) := by
  refine ⟨.branch sv (edgeKids base.sd old rest) oldMem,hs,rfl,?_⟩
  have hwin := windows_eq_of_occupancy (edge_occupancy base.sd old new rest ho hn)
  have hshape : nonemptyFields (nodeRawShape (.branch sv (edgeKids base.sd old rest) oldMem))=
      (encodePart base (.branch sv (edgeKids base.sd old rest) oldMem)
        (.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem)).shape := by
    cases sv <;> simp [encodePart,nonempty_node_shape,nodeTypeCode,nodeChildren,hwin,NodeGen3.hplenOf,NodeGen3.isLE]
  rw [←hshape]
  change LayoutEdit base.kind _ _
  rw [hk]
  exact LayoutEdit.preserve 0 (by simp) _

def rdb_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=0)
    (sd : base.sd=0 ∨ base.sd=1)
    (sv : Option NSlot3) (rest : List NKid) (old new : NKid) (oldMem newMem : List Nat)
    (ho : old≠.none) (hn : new≠.none) (how : old.wf) (hnw : new.wf)
    (hs : (NodeV3.branch sv (edgeKids base.sd old rest) oldMem).wf)
    (hd : (NodeV3.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem).wf)
    (hbytes : ∀b∈(NodeV3.branch sv (edgeKids base.sd old rest) oldMem).ser true,b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.branch sv (edgeKids base.sd old rest) oldMem)
      (.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem)) := by
  let Q := encodePart base (.branch sv (edgeKids base.sd old rest) oldMem)
    (.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem)
  let enc := encodePart_encoding base (.branch sv (edgeKids base.sd old rest) oldMem)
    (.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem) hd
  let src := rdb_sourceLayout base hk sv rest old new oldMem newMem ho hn hs
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
    copyFields := rdb_copy I base hk sd sv rest old new oldMem newMem ho hn how hnw hs hd }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · refine ⟨?_⟩
    intro _ h; simp [VcpB,Q,encodePart,hk] at h
  · refine ⟨hx,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro h; simp [HeaderNeeded,XcpB,Q,encodePart,hk] at h
  · intro h; simp [Q,encodePart,hk] at h
  · intro ht _
    let v := sv.getD default
    have hslot : sv=some v := by
      cases hh : sv with
      | none => simp [Q,encodePart,hh,nodeTypeCode] at ht
      | some x => simp [v,hh]
    refine ⟨src,?_,rfl,?_⟩
    · change ValueEdit base.kind I.ci (.branch sv (edgeKids base.sd old rest) oldMem)
        (.branch (sv.map snapshotValue) (edgeKids base.sd new (rest.map snapshotKid)) newMem)
      rw [hk,hslot]
      exact ValueEdit.branch 0 I.ci (by simp) _ _ _ _ _ _
    · simp [Q,encodePart,valueOffset,src,rdb_sourceLayout,hslot,NodeGen3.isLeaf]

end ZkFormal.NearV3.Render.UpsGen
