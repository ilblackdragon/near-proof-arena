import ZkFormal.NearV3.Render.Ups.EncodePart
import ZkFormal.NearV3.Render.Ups.CopyFields

/-! Newly created leaf/extension nodes inherit no source payload. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render

theorem nlf_copy (I : UpsInst) (base : UpsPartI) (hk : base.kind=8)
    (src : NodeV3) (key : List Nat) (sv : NSlot3) (mem : List Nat) :
    CopyFields I (encodePart base src (.leaf key sv mem)) := by
  constructor
  intro pre post st width hshape hcopy
  have hm : (st,width) ∈ (encodePart base src (.leaf key sv mem)).shape := by
    rw [hshape]; simp
  have hs : st≠7 := by
    intro he
    subst st
    simp [encodePart,nonemptyFields,nodeRawShape,NodeGen3.fieldsOf,
      NodeGen.F.state,NodeGen.F.len,Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sVLEN,Node.sVH,Node.sMEM] at hm
  simp [CpB,WfrB,VcpB,encodePart,hk,hs] at hcopy

theorem wex_copy (I : UpsInst) (base : UpsPartI) (hk : base.kind=9)
    (src : NodeV3) (key : List Nat) (kid : NKid) (mem : List Nat) :
    CopyFields I (encodePart base src (.ext key kid mem)) := by
  constructor
  intro pre post st width hshape hcopy
  simp [CpB,WfrB,VcpB,encodePart,hk] at hcopy

end ZkFormal.NearV3.Render.UpsGen
