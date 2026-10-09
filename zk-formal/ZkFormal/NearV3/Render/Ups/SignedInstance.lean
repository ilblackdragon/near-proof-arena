import ZkFormal.NearV3.Render.Ups.NativePartEncoding
import ZkFormal.NearV3.Render.Ups.FieldEnd

namespace ZkFormal.NearV3.Render.UpsGen

/-- Fill the honest subtraction sign after constructing the complete source table. -/
def signedInstance (I : UpsInst) : UpsInst := {I with parts:=I.parts.map (withMemorySign I)}

@[simp] theorem signedInstance_child_pb (I : UpsInst) (Q : UpsPartI) :
    (child (signedInstance I) Q).pb=(child I Q).pb := by
  simp only [child,part,signedInstance,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases I.parts[Q.jm-1]? <;> rfl

@[simp] theorem signedInstance_X1V (I : UpsInst) (Q : UpsPartI) : X1V (signedInstance I) Q=X1V I Q := by
  funext i
  simp only [X1V,Ai,Bi,Ci,memByte,signedInstance_child_pb]
  rfl

@[simp] theorem signedInstance_EinV (I : UpsInst) (Q : UpsPartI) : EinV (signedInstance I) Q=EinV I Q := rfl

theorem MemOk.signedInstance {I : UpsInst} {Q : UpsPartI} (h : MemOk I Q) : MemOk (UpsGen.signedInstance I) Q := by
  constructor
  · intro i hi
    simpa only [cbV,coV,co2V,TV,tV,RV,signedInstance_X1V,signedInstance_EinV] using h.carries i hi
  · intro p hp hs
    simpa only [RV,TV,signedInstance_X1V,signedInstance_EinV] using h.bytes p hp hs

def SourceHeader.withParts {I : UpsInst} {Q : UpsPartI} {e : SourceLayout Q}
    (h : SourceHeader I Q e) (parts : List UpsPartI) : SourceHeader {I with parts:=parts} Q e :=
  ⟨h.hplen,h.odd,h.prefixNode,h.leaf,h.insertValue⟩

/-- Byte semantics depend on the source/output payloads and terminal metadata,
so populating the surrounding part table preserves them. -/
def ByteInput.withParts {I : UpsInst} {Q : UpsPartI} (data : ByteInput I Q) (parts : List UpsPartI) :
    ByteInput {I with parts:=parts} Q where
  output := data.output
  kind := data.kind
  nochild := data.nochild
  freshPrefix := ⟨data.freshPrefix.terminal,data.freshPrefix.leaf,data.freshPrefix.wrap,data.freshPrefix.pass⟩
  freshValue := ⟨data.freshValue.slot⟩
  splitBitmap := ⟨data.splitBitmap.xbound,data.splitBitmap.slots,data.splitBitmap.distinct⟩
  sourceBytes := data.sourceBytes
  sourceLayout := data.sourceLayout
  sourceHeader h := ⟨(data.sourceHeader h).val,(data.sourceHeader h).property.withParts parts⟩
  movedPrefix h := ⟨(data.movedPrefix h).source,(data.movedPrefix h).header.withParts parts,
    (data.movedPrefix h).key,(data.movedPrefix h).leaf,(data.movedPrefix h).prefixNode⟩
  sourceValue ht hv := ⟨(data.sourceValue ht hv).source,(data.sourceValue ht hv).edit,
    (data.sourceValue ht hv).hplen,(data.sourceValue ht hv).offset⟩
  copyFields := ⟨data.copyFields.fields⟩

/-- The honest global sign pass preserves each already constructed byte/memory input. -/
def ByteMemoryInput.signedInstance {I : UpsInst} {Q : UpsPartI}
    (data : ByteMemoryInput I (withMemorySign I Q)) :
    ByteMemoryInput (UpsGen.signedInstance I) (withMemorySign I Q) :=
  ⟨data.bytes.withParts _,data.memory.signedInstance⟩

/-- Per-part plans ignore the constructed subtraction sign and other parts' signs. -/
def PartOk.signedInstance {I : UpsInst} {k : Nat} {Q : UpsPartI} (h : PartOk I k Q) :
    PartOk (UpsGen.signedInstance I) k (withMemorySign I Q) where
  kind := h.kind
  kindT := h.kindT
  kindU := h.kindU
  pdepT := h.pdepT
  pdepU := h.pdepU
  rcT := h.rcT
  sd := h.sd
  sdRD := h.sdRD
  sdT := h.sdT
  sN := h.sN
  pdepS := h.pdepS
  ty := h.ty
  tyBr := h.tyBr
  tyBV := h.tyBV
  tyExt := h.tyExt
  tyLeaf := h.tyLeaf
  tySpb := h.tySpb
  pt := h.pt
  spbKids := h.spbKids
  nlf := h.nlf
  wex := h.wex
  mv := h.mv
  mveOdd := h.mveOdd
  xcp := h.xcp
  jmD := h.jmD
  jmS := h.jmS
end ZkFormal.NearV3.Render.UpsGen
