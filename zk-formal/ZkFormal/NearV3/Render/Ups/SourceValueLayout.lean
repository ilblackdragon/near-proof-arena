import ZkFormal.NearV3.Render.Ups.ValueFieldPosition
import ZkFormal.NearV3.Render.Ups.SourceLayout

/-! Value-read alignment follows the source and output node forms. The source offset
is the actual serialized value-slot position, independently of register constraints. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

inductive ValueEdit : Nat → Nat → NodeV3 → NodeV3 → Prop
  | branch (kind ci : Nat) (hk : kind ∈ [0,3,5]) (sv dv sk dk sm dm) :
      ValueEdit kind ci (.branch (some sv) sk sm) (.branch (some dv) dk dm)
  | moved (ci : Nat) (sk dk sv dv sm dm) : ValueEdit 6 ci (.leaf sk sv sm) (.leaf dk dv dm)
  | split (sk sv sm dv dk dm) : ValueEdit 10 4 (.leaf sk sv sm) (.branch (some dv) dk dm)

structure SourceValueLayout (I : UpsInst) (Q : UpsPartI) (dst : NodeEncoding Q) where
  source : SourceLayout Q
  edit : ValueEdit Q.kind I.ci source.node dst.node
  hplen : Q.phk=NodeGen3.hplenOf source.node
  offset : Q.soff=if NodeGen3.isLeaf source.node then 5+NodeGen3.hplenOf source.node else 1

theorem leaf_serial_length (key : List Nat) (sv : NSlot3) (mem : List Nat)
    (hw : (NodeV3.leaf key sv mem).wf) :
    ((NodeV3.leaf key sv mem).ser true).length=49+NodeGen3.hplenOf (.leaf key sv mem) := by
  rw [NodeGen3.ser_len hw true]
  simp [NodeGen.layout,NodeGen3.fieldsOf,NodeGen.F.len,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf]
  omega

theorem SourceValueLayout.position {I : UpsInst} {Q : UpsPartI} {dst : NodeEncoding Q}
    (m : SourceValueLayout I Q dst) (f : FieldsOk Q) {p : Nat}
    (hs : (fieldAt Q.shape p).1=4) :
    sposV I Q 4 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p =
      ((Q.soff + (fieldAt Q.shape p).2.1 : Nat) : Int) := by
  have htype := dst.ty
  have hsrc := m.source.bytes
  have hph := m.hplen
  have hoff := m.offset
  have hedit := m.edit
  have hw := m.source.wf
  generalize hk0 : Q.kind=kind at hedit
  generalize hc0 : I.ci=ci at hedit
  generalize hn0 : m.source.node=src at hedit hsrc hph hoff hw
  generalize hn1 : dst.node=dn at hedit htype
  cases hedit with
  | branch kind ci hk sv dv sk dk sm dm =>
    have ht : Q.ty=3 := by simpa [nodeTypeCode] using htype
    have hp := f.vlen_position (Or.inr ht) hs
    have ho : Q.soff=1 := by simpa [NodeGen3.isLeaf] using hoff
    rcases (show Q.kind=0 ∨ Q.kind=3 ∨ Q.kind=5 by simpa [← hk0] using hk) with hk | hk | hk <;>
      simp [sposV,hk,aftV,AftB,ind] <;> simp [ht] at hp <;> omega
  | moved ci sk dk sv dv sm dm =>
    have ht : Q.ty=0 := by simpa [nodeTypeCode] using htype
    have hp := f.vlen_position (Or.inl ht) hs
    have ho : Q.soff=5+Q.phk := by simpa [NodeGen3.isLeaf,← hph] using hoff
    simp [sposV,hk0] <;> simp [ht] at hp <;> omega
  | split sk sv sm dv dk dm =>
    have ht : Q.ty=3 := by simpa [nodeTypeCode] using htype
    have hp := f.vlen_position (Or.inr ht) hs
    have ho : Q.soff=5+Q.phk := by simpa [NodeGen3.isLeaf,← hph] using hoff
    have hl : Q.pb.length=49+Q.phk := by rw [hsrc,leaf_serial_length _ _ _ hw,← hph]
    simp [sposV,hk0] <;> simp [ht] at hp <;> omega

end ZkFormal.NearV3.Render.UpsGen
