import ZkFormal.NearV3.Render.Ups.RbiCopy
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def rbi_sourceLayout (I : UpsInst) (base : UpsPartI) (hk : base.kind=5)
    (sv : Option NSlot3) (rest : List NKid) (new : NKid) (oldMem newMem : List Nat)
    (hn : new≠.none)
    (hs : (NodeV3.branch sv (edgeKids (insertSide I) .none rest) oldMem).wf) :
    SourceLayout (encodePart base (.branch sv (edgeKids (insertSide I) .none rest) oldMem)
      (.branch (sv.map snapshotValue) (edgeKids (insertSide I) new (rest.map snapshotKid)) newMem)) := by
  refine ⟨.branch sv (edgeKids (insertSide I) .none rest) oldMem,hs,rfl,?_⟩
  have hwin := edge_insert_windows (insertSide I) rest new hn
  change LayoutEdit base.kind _ _
  rw [hk]
  simp only [encodePart,nonempty_node_shape,nodeChildren,hwin]
  cases sv <;> simp only [Option.map_none,Option.map_some,nodeTypeCode,NodeGen3.hplenOf,NodeGen3.isLE,
    Bool.false_eq_true,ite_false,nodeFields_eq_header,List.replicate_succ,List.cons_append]
  all_goals exact LayoutEdit.child _ _

def rbi_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=5)
    (sv : Option NSlot3) (rest : List NKid) (new : NKid) (oldMem newMem : List Nat)
    (hn : new≠.none) (hnw : new.wf)
    (hs : (NodeV3.branch sv (edgeKids (insertSide I) .none rest) oldMem).wf)
    (hd : (NodeV3.branch (sv.map snapshotValue) (edgeKids (insertSide I) new (rest.map snapshotKid)) newMem).wf)
    (hbytes : ∀b∈(NodeV3.branch sv (edgeKids (insertSide I) .none rest) oldMem).ser true,b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.branch sv (edgeKids (insertSide I) .none rest) oldMem)
      (.branch (sv.map snapshotValue) (edgeKids (insertSide I) new (rest.map snapshotKid)) newMem)) := by
  let Q := encodePart base (.branch sv (edgeKids (insertSide I) .none rest) oldMem)
    (.branch (sv.map snapshotValue) (edgeKids (insertSide I) new (rest.map snapshotKid)) newMem)
  let enc := encodePart_encoding base (.branch sv (edgeKids (insertSide I) .none rest) oldMem)
    (.branch (sv.map snapshotValue) (edgeKids (insertSide I) new (rest.map snapshotKid)) newMem) hd
  let src := rbi_sourceLayout I base hk sv rest new oldMem newMem hn hs
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
    copyFields := rbi_copy I base hk sv rest new oldMem newMem hn hnw hs hd }
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
    · change ValueEdit base.kind I.ci (.branch sv (edgeKids (insertSide I) .none rest) oldMem)
        (.branch (sv.map snapshotValue) (edgeKids (insertSide I) new (rest.map snapshotKid)) newMem)
      rw [hk,hslot]
      exact ValueEdit.branch 5 I.ci (by simp) _ _ _ _ _ _
    · simp [Q,encodePart,valueOffset,src,rbi_sourceLayout,hslot,NodeGen3.isLeaf]

end ZkFormal.NearV3.Render.UpsGen
