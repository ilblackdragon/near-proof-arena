import ZkFormal.NearV3.Render.Ups.NodeFieldsBridge

/-! Canonical byte-facing part data extracted from actual source/output nodes.
Plan and memory metadata stay in the base record; no byte constraint is assumed. -/
namespace ZkFormal.NearV3.Render.UpsGen

/-- Actual value-length offset in a serialized source node (zero when no value exists). -/
def valueOffset : NodeV3 → Nat
  | .leaf key sv mem => 5+NodeGen3.hplenOf (.leaf key sv mem)
  | .branch (some _) .. => 1
  | _ => 0

def encodePart (base : UpsPartI) (src dst : NodeV3) : UpsPartI :=
  { base with
    pb := src.ser true
    ty := nodeTypeCode dst
    qhk := NodeGen3.hplenOf dst
    qodd := NodeGen3.oddOf dst
    phk := NodeGen3.hplenOf src
    podd := NodeGen3.oddOf src
    nochild := if nodeChildren dst=0 then 1 else 0
    shape := nonemptyFields (nodeRawShape dst)
    q := dst.ser false
    soff := valueOffset src }

def encodePart_encoding (base : UpsPartI) (src dst : NodeV3) (hw : dst.wf) :
    NodeEncoding (encodePart base src dst) :=
  ⟨dst,hw,rfl,rfl,rfl,rfl,rfl⟩

theorem encodePart_fields (base : UpsPartI) (src dst : NodeV3) (hw : dst.wf) :
    FieldsOk (encodePart base src dst) :=
  (encodePart_encoding base src dst hw).fieldsOk rfl

end ZkFormal.NearV3.Render.UpsGen
