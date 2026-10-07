import ZkFormal.NearV3.Render.Ups.PtCopy
import ZkFormal.NearV3.Render.Ups.GBytes

/-! Construct ByteInput for actual extension child replacement. Only the ordinary source
byte bounds, node well-formedness, and terminal and nibble bounds remain inputs here;
all copy/layout/header obligations are derived from the source/output leaf forms. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

def pt_sourceLayout (base : UpsPartI) (hk : base.kind=11)
    (old new : NKid) (oldMem newMem : List Nat)
    (hw : (NodeV3.ext [] old oldMem).wf) :
    SourceLayout (encodePart base (.ext [] old oldMem) (.ext [] new newMem)) := by
  refine ⟨.ext [] old oldMem,hw,rfl,?_⟩
  have hshape : nonemptyFields (nodeRawShape (.ext [] old oldMem)) =
      (encodePart base (.ext [] old oldMem) (.ext [] new newMem)).shape := by
    simp [encodePart,nodeRawShape,NodeGen3.fieldsOf,NodeGen.F.state,NodeGen.F.len,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf]
  rw [← hshape]
  change LayoutEdit base.kind _ _
  rw [hk]
  exact LayoutEdit.preserve 11 (by simp) _

/-- Byte renderer completeness inputs for the actual `ext(key,old) → ext(key,new)` edit. -/
def pt_byteInput (I : UpsInst) (base : UpsPartI) (hk : base.kind=11)
    (old new : NKid) (oldMem newMem : List Nat)
    (hs : (NodeV3.ext [] old oldMem).wf) (hd : (NodeV3.ext [] new newMem).wf)
    (hbytes : ∀ b ∈ (NodeV3.ext [] old oldMem).ser true, b<256)
    (hts : 1≤I.ts ∧ I.ts≤3) (hx : I.x<16) :
    ByteInput I (encodePart base (.ext [] old oldMem) (.ext [] new newMem)) := by
  let Q := encodePart base (.ext [] old oldMem) (.ext [] new newMem)
  let enc := encodePart_encoding base (.ext [] old oldMem) (.ext [] new newMem) hd
  refine {
    output := enc
    kind := by simp [Q,encodePart,hk]
    nochild := rfl
    freshPrefix := ?_
    freshValue := ?_
    splitBitmap := ?_
    sourceBytes := hbytes
    sourceLayout := fun _ => pt_sourceLayout base hk old new oldMem newMem hs
    sourceHeader := ?_
    movedPrefix := ?_
    sourceValue := ?_
    copyFields := pt_copy I base hk [] old new oldMem newMem hd }
  · refine ⟨hts,?_,?_,?_⟩ <;> simp [Q,encodePart,hk,enc,encodePart_encoding,NodeGen3.keyOf,NodeGen3.isLeaf]
  · refine ⟨?_⟩
    intro h
    simp [Q,encodePart,nodeTypeCode] at h
  · refine ⟨hx,?_,?_⟩ <;> simp [Q,encodePart,hk]
  · intro h
    simp [HeaderNeeded,XcpB,Q,encodePart,hk] at h
  · intro h
    simp [Q,encodePart,hk] at h
  · intro h
    simp [VcpB,Q,encodePart,hk] at h

end ZkFormal.NearV3.Render.UpsGen
