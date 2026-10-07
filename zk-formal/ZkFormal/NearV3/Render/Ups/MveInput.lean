import ZkFormal.NearV3.Render.Ups.MveCopy
import ZkFormal.NearV3.Render.Ups.GBytes

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def mve_sourceLayout (I : UpsInst) (base : UpsPartI) (hk : base.kind=7)
    (key : List Nat) (sv : NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.ext key sv oldMem).wf) :
    SourceLayout (encodePart base (.ext key sv oldMem)
      (.ext (key.drop (I.ti+1)) (snapshotKid sv) newMem)) := by
  refine ⟨.ext key sv oldMem,hs,rfl,?_⟩
  change LayoutEdit base.kind _ _
  rw [hk]
  exact LayoutEdit.other 7 (by simp) _ _

def mve_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=7)
    (key : List Nat) (sv : NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.ext key sv oldMem).wf)
    (hd : (NodeV3.ext (key.drop (I.ti+1)) (snapshotKid sv) newMem).wf)
    (hcut : I.ti+1≤key.length)
    (hbytes : ∀ b ∈ (NodeV3.ext key sv oldMem).ser true, b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.ext key sv oldMem)
      (.ext (key.drop (I.ti+1)) (snapshotKid sv) newMem)) := by
  let Q := encodePart base (.ext key sv oldMem) (.ext (key.drop (I.ti+1)) (snapshotKid sv) newMem)
  let enc := encodePart_encoding base (.ext key sv oldMem) (.ext (key.drop (I.ti+1)) (snapshotKid sv) newMem) hd
  let src := mve_sourceLayout I base hk key sv oldMem newMem hs
  have header : SourceHeader I Q src := by
    refine ⟨rfl,rfl,?_,?_,?_⟩
    · intro _; rfl
    · intro _; simp [Q,encodePart,nodeTypeCode,src,mve_sourceLayout,NodeGen3.isLeaf]
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
    copyFields := mve_copy I base hk key sv oldMem newMem hs hd hcut }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · refine ⟨?_⟩
    intro h _; simp [Q,encodePart,nodeTypeCode] at h
  · refine ⟨hx,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro h; simp [Q,encodePart,hk] at h
  · intro h _; simp [Q,encodePart,nodeTypeCode] at h

end ZkFormal.NearV3.Render.UpsGen
