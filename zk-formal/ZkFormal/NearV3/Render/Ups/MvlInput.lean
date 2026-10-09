import ZkFormal.NearV3.Render.Ups.MvlCopy
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def mvl_sourceLayout (I : UpsInst) (base : UpsPartI) (hk : base.kind=6)
    (key : List Nat) (sv : NSlot3) (oldMem newMem : List Nat)
    (hs : (NodeV3.leaf key sv oldMem).wf) :
    SourceLayout (encodePart base (.leaf key sv oldMem)
      (.leaf (key.drop (I.ti+1)) (snapshotValue sv) newMem)) := by
  refine ⟨.leaf key sv oldMem,hs,rfl,?_⟩
  change LayoutEdit base.kind _ _
  rw [hk]
  exact LayoutEdit.other 6 (by simp) _ _

def mvl_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=6)
    (key : List Nat) (sv : NSlot3) (oldMem newMem : List Nat)
    (hs : (NodeV3.leaf key sv oldMem).wf)
    (hd : (NodeV3.leaf (key.drop (I.ti+1)) (snapshotValue sv) newMem).wf)
    (hcut : I.ti+1≤key.length)
    (hbytes : ∀ b ∈ (NodeV3.leaf key sv oldMem).ser true, b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.leaf key sv oldMem)
      (.leaf (key.drop (I.ti+1)) (snapshotValue sv) newMem)) := by
  let Q := encodePart base (.leaf key sv oldMem) (.leaf (key.drop (I.ti+1)) (snapshotValue sv) newMem)
  let enc := encodePart_encoding base (.leaf key sv oldMem) (.leaf (key.drop (I.ti+1)) (snapshotValue sv) newMem) hd
  let src := mvl_sourceLayout I base hk key sv oldMem newMem hs
  have header : SourceHeader I Q src := by
    refine ⟨rfl,rfl,?_,?_,?_⟩
    · intro _; rfl
    · intro _; simp [Q,encodePart,nodeTypeCode,src,mvl_sourceLayout,NodeGen3.isLeaf]
    · simp [Q,encodePart,hk]
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ?_
    splitBitmap := ?_
    sourceBytes := hbytes
    sourceLayout := ?_
    sourceHeader := fun _ => ⟨src,header⟩
    movedPrefix := fun _ => ⟨src,header,rfl,rfl,rfl⟩
    sourceValue := ?_
    copyFields := mvl_copy I base hk key sv oldMem newMem hs hd hcut }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · refine ⟨?_⟩
    intro _ h; simp [VcpB,Q,encodePart,hk] at h
  · refine ⟨hx,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro h; simp [Q,encodePart,hk] at h
  · intro _ _
    refine ⟨src,?_,rfl,rfl⟩
    change ValueEdit base.kind I.ci (.leaf key sv oldMem)
      (.leaf (key.drop (I.ti+1)) (snapshotValue sv) newMem)
    rw [hk]
    exact ValueEdit.moved I.ci key (key.drop (I.ti+1)) sv (snapshotValue sv) oldMem newMem

end ZkFormal.NearV3.Render.UpsGen
