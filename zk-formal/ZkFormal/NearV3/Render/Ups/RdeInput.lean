import ZkFormal.NearV3.Render.Ups.RdeCopy
import ZkFormal.NearV3.Render.Ups.GBytes

/-! Construct ByteInput for actual extension child replacement. Only the ordinary source
byte bounds, node well-formedness, and terminal and nibble bounds remain inputs here;
all copy/layout/header obligations are derived from the source/output leaf forms. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def rde_sourceLayout (base : UpsPartI) (hk : base.kind=1)
    (key : List Nat) (old new : NKid) (oldMem newMem : List Nat)
    (hw : (NodeV3.ext key old oldMem).wf) :
    SourceLayout (encodePart base (.ext key old oldMem) (.ext key new newMem)) := by
  refine ⟨.ext key old oldMem,hw,rfl,?_⟩
  have hshape : nonemptyFields (nodeRawShape (.ext key old oldMem)) =
      (encodePart base (.ext key old oldMem) (.ext key new newMem)).shape := by
    simp [encodePart,nodeRawShape,NodeGen3.fieldsOf,NodeGen.F.state,NodeGen.F.len,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf]
  rw [← hshape]
  change LayoutEdit base.kind _ _
  rw [hk]
  exact LayoutEdit.preserve 1 (by simp) _

/-- Byte renderer completeness inputs for the actual `ext(key,old) → ext(key,new)` edit. -/
def rde_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=1)
    (key : List Nat) (old new : NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.ext key old oldMem).wf) (hd : (NodeV3.ext key new newMem).wf)
    (hbytes : ∀ b ∈ (NodeV3.ext key old oldMem).ser true, b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.ext key old oldMem) (.ext key new newMem)) := by
  let Q := encodePart base (.ext key old oldMem) (.ext key new newMem)
  let enc := encodePart_encoding base (.ext key old oldMem) (.ext key new newMem) hd
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ?_
    splitBitmap := ?_
    sourceBytes := hbytes
    sourceLayout := fun _ => rde_sourceLayout base hk key old new oldMem newMem hs
    sourceHeader := ?_
    movedPrefix := ?_
    sourceValue := ?_
    copyFields := rde_copy I base hk key old new oldMem newMem hd }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · refine ⟨?_⟩
    intro h
    simp [Q,encodePart,nodeTypeCode] at h
  · refine ⟨hx,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro h
    simp [HeaderNeeded,XcpB,Q,encodePart,hk] at h
  · intro h
    simp [Q,encodePart,hk] at h
  · intro _ h
    simp [VcpB,Q,encodePart,hk] at h

end ZkFormal.NearV3.Render.UpsGen
