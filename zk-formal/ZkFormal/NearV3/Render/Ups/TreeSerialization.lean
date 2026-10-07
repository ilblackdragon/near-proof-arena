import ZkFormal.NearV3.Render.Ups.TreePartEncoding

/-! Exact runtime serialization only needs the shallow view's structural well-formedness.
In particular it does not require a newly computed native memory total to be below u64. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

theorem treeNode_ser_of_view {t : PTrie} {node : NodeV3}
    (hn : treeNode t=some node) (hw : node.wf) (post : Bool) :
    node.ser post=(nodeEnc t).map UInt8.toNat := by
  cases t with
  | hash => simp [treeNode] at hn
  | leaf key value mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp [NodeV3.ser,nodeEnc,u32Bytes,hpN]
  | ext key child mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp [NodeV3.ser,nodeEnc,u32Bytes,hpN]
  | branch value kids mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    have hb := Link.kidBitmap_lt hw.1
    rw [treeKids_bitmap] at hb
    cases value <;> simp [NodeV3.ser,nodeEnc,map_u16_small _ hb]

/-- Shallow output correctness suffices to recover both native serialized preimages. -/
theorem encodeTreePart_bytes_of_view {base Q : UpsPartI} {part : TreePart} {dst : NodeV3}
    (he : encodeTreePart base part=some Q) (hs : part.source.wf=true)
    (hd : treeNode part.output=some dst) (hw : dst.wf) :
    Q.pb=(nodeEnc part.source).map UInt8.toNat ∧ Q.q=(nodeEnc part.output).map UInt8.toNat := by
  unfold encodeTreePart at he
  cases hsrc : treeNode part.source with
  | none => simp [hsrc] at he
  | some src =>
    simp [hsrc,hd] at he
    subst Q
    exact ⟨treeNode_ser hs hsrc true,treeNode_ser_of_view hd hw false⟩
end ZkFormal.NearV3.Render.UpsGen
