import ZkFormal.NearV3.Render.Ups.RlpCopy
import ZkFormal.NearV3.Render.Ups.GBytes

/-! Construct ByteInput for actual leaf value replacement. Only the ordinary source
byte bounds, node well-formedness, and new value-slot length remain inputs here;
all copy/layout/header obligations are derived from the source/output leaf forms. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def rlp_sourceLayout (base : UpsPartI) (hk : base.kind=2)
    (key : List Nat) (old new : NSlot3) (oldMem newMem : List Nat)
    (hw : (NodeV3.leaf key old oldMem).wf) :
    SourceLayout (encodePart base (.leaf key old oldMem) (.leaf key new newMem)) := by
  refine ⟨.leaf key old oldMem,hw,rfl,?_⟩
  have hshape : nonemptyFields (nodeRawShape (.leaf key old oldMem)) =
      (encodePart base (.leaf key old oldMem) (.leaf key new newMem)).shape := by
    simp [encodePart,nodeRawShape,NodeGen3.fieldsOf,NodeGen.F.state,NodeGen.F.len,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf]
  rw [← hshape]
  change LayoutEdit base.kind _ _
  rw [hk]
  exact LayoutEdit.preserve 2 (by simp) _

/-- Byte renderer completeness inputs for the actual `leaf(key,old) → leaf(key,new)` edit. -/
def rlp_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=2)
    (key : List Nat) (old new : NSlot3) (oldMem newMem : List Nat)
    (hs : (NodeV3.leaf key old oldMem).wf) (hd : (NodeV3.leaf key new newMem).wf)
    (hlen : new.lenB=(NearSpec.u32 (L I)).map UInt8.toNat)
    (hbytes : ∀ b ∈ (NodeV3.leaf key old oldMem).ser true, b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.leaf key old oldMem) (.leaf key new newMem)) := by
  let Q := encodePart base (.leaf key old oldMem) (.leaf key new newMem)
  let enc := encodePart_encoding base (.leaf key old oldMem) (.leaf key new newMem) hd
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ?_
    splitBitmap := ?_
    sourceBytes := hbytes
    sourceLayout := fun _ => rlp_sourceLayout base hk key old new oldMem newMem hs
    sourceHeader := ?_
    movedPrefix := ?_
    sourceValue := ?_
    copyFields := rlp_copy I base hk key old new oldMem newMem hd }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · refine ⟨?_⟩
    intro _ _
    exact ⟨new,rfl,hlen⟩
  · refine ⟨hx,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro h
    simp [HeaderNeeded,XcpB,Q,encodePart,hk] at h
  · intro h
    simp [Q,encodePart,hk] at h
  · intro h
    simp [VcpB,Q,encodePart,hk] at h

end ZkFormal.NearV3.Render.UpsGen
