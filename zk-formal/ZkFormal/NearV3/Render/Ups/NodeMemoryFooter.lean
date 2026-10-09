import ZkFormal.NearV3.Render.Ups.TreeMemConstruct

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

theorem node_ser_memory_suffix (node : NodeV3) (post : Bool) :
    ∃ frontBytes,node.ser post=frontBytes++NodeGen3.memOf node := by
  cases node with
  | leaf key value mem =>
    refine ⟨[0]++u32Bytes (hpN key true).length++hpN key true++value.bytes post,?_⟩
    rfl
  | ext key kid mem =>
    refine ⟨[3]++u32Bytes (hpN key false).length++hpN key false++kid.bytes post,?_⟩
    rfl
  | branch value kids mem =>
    refine ⟨(match value with | none => [1] | some s => [2]++s.bytes post) ++
      [kidBitmap kids%256,kidBitmap kids/256]++kids.flatMap (NKid.bytes post),?_⟩
    rfl

theorem node_memory_footer (node : NodeV3) (post : Bool) (hm : (NodeGen3.memOf node).length=8) :
    (node.ser post).drop ((node.ser post).length-8)=NodeGen3.memOf node := by
  obtain ⟨frontBytes,hfront⟩ := node_ser_memory_suffix node post
  rw [hfront,List.length_append,hm]
  simp

theorem NodeEncoding.memory_length {Q : UpsPartI} (e : NodeEncoding Q) :
    (NodeGen3.memOf e.node).length=8 := by
  have hw := e.wf
  cases hn : e.node <;> simp_all [NodeV3.wf,NodeGen3.memOf]

/-- The ordinary output encoding fixes its u64 footer even if the native exact
memory total exceeds u64. Full node injectivity is unnecessary for this fact. -/
theorem NodeEncoding.native_memory {base Q : UpsPartI} {part : TreePart}
    (e : NodeEncoding Q) (he : encodeTreePart base part=some Q) :
    NodeGen3.memOf e.node=(u64 part.output.memD).map UInt8.toNat := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source with
  | none => simp [hs] at he
  | some src =>
    cases hd : treeNode part.output with
    | none => simp [hs,hd] at he
    | some dst =>
      simp [hs,hd] at he
      subst Q
      have hbytes : dst.ser false=e.node.ser false := e.bytes
      have hmd : (NodeGen3.memOf dst).length=8 := by rw [treeNode_memory hd]; simp
      have hf := congrArg (fun xs : List Nat => xs.drop (xs.length-8)) hbytes
      rw [node_memory_footer dst false hmd,node_memory_footer e.node false e.memory_length] at hf
      exact hf.symm.trans (treeNode_memory hd)
end ZkFormal.NearV3.Render.UpsGen
