import ZkFormal.NearV3.Render.Ups.MemTotalBounds
import ZkFormal.NearV3.Render.Ups.TreeSerialization
import ZkFormal.NearV3.Render.Ups.MemNative

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

theorem treeNode_memory {t : PTrie} {node : NodeV3} (he : treeNode t=some node) :
    NodeGen3.memOf node=(u64 t.memD).map UInt8.toNat := by
  cases t <;> simp [treeNode] at he
  all_goals subst node; rfl

/-- Assemble memory constraints after the concrete native constructor proves its
scalar formula. Exact totals are serialized modulo u64; only shallow output
structure is required, not native output wf or output memory fitting in u64. -/
theorem encodeTreePart_memOk (I : UpsInst) (base Q : UpsPartI) (part : TreePart) (dst : NodeV3)
    (he : encodeTreePart base part=some Q) (hw : part.source.wf=true)
    (hd : treeNode part.output=some dst) (hwd : dst.wf)
    (hk : Q.kind<12) (hc : I.ci<11) (hq : Q.qhk<2^22) (hp : Q.phk<2^22)
    (hL : L I<2^24) (hchild : ∀ b∈(child I Q).pb,b<256) (hm : Q.mB<2^74)
    (hr : RV I (withMemorySign I Q)=(part.output.memD:Int)) : MemOk I (withMemorySign I Q) := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source with
  | none => simp [hs] at he
  | some src =>
    simp [hs,hd] at he
    subst Q
    let e := encodePart_encoding {base with kind:=part.kind.ix} src dst hwd
    refine construct_memOk_bounded I _ e hk hc hq hp hL
      (treeNode_byte_bound hw hs true) hchild ?_ hm ?_
    · change ∀ b∈NodeGen3.memOf dst,b<256
      rw [treeNode_memory hd]
      intro b hb; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb; exact x.toNat_lt
    · rw [← withMemorySign_RV,hr]
      change (part.output.memD:Int)%256^8=(le256 (NodeGen3.memOf dst):Int)
      rw [treeNode_memory hd,u64_memory_decode]
      omega
end ZkFormal.NearV3.Render.UpsGen
