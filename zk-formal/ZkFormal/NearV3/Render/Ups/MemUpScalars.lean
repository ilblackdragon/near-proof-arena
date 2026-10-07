import ZkFormal.NearV3.Render.Ups.MemNative

namespace ZkFormal.NearV3.Render.UpsGen

/-- Propagating a child update uses exact new memory and the serialized old child,
with native subtraction clamping after the addition. -/
theorem up_memory_scalar (I : UpsInst) (Q : UpsPartI) (hL : L I<2^24)
    (hk : Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=11)
    (m old : Nat) (hm : pfx (memRb Q) 8=(m:Int))
    (ho : pfx (memByte (child I Q)) 8=(old:Int)) :
    RV I (withMemorySign I Q)=((m+Q.mB-old:Nat):Int) := by
  rw [withMemorySign_RV,memory_subtraction_scalar I Q hL,memory_base_scalar I Q hL]
  rcases hk with hk|hk|hk <;>
    simp [useAV,bNV,bLV,cOV,cSV,CcV,eLV,eSV,KcV,kin,xcpV,XcpB,ind,hk,hm,ho] <;>
    split <;> omega

/-- A source serialized as a real node has at least its eight memory bytes. -/
theorem encoded_source_length {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) (hw : part.source.wf=true) : 8≤Q.pb.length := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source with
  | none => simp [hs] at he
  | some src =>
    cases hd : treeNode part.output with
    | none => simp [hs,hd] at he
    | some dst =>
      simp [hs,hd] at he
      subst Q
      have hn : isNode part.source=true := by
        cases h : part.source <;> simp_all [treeNode,isNode]
      obtain ⟨frontBytes,hfront⟩ := nodeEnc_memory_suffix part.source hn
      change 8≤(src.ser true).length
      rw [treeNode_ser hw hs true,hfront]
      simp

theorem memByte_eq_memRb (Q : UpsPartI) (hl : 8≤Q.pb.length) : memByte Q=memRb Q := by
  funext i
  unfold memByte memRb
  congr 2
  omega

theorem encoded_child_memory {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) (hw : part.source.wf=true) :
    pfx (memByte Q) 8=(part.source.memD:Int) := by
  rw [memByte_eq_memRb Q (encoded_source_length he hw)]
  exact encoded_source_memory_exact he hw
end ZkFormal.NearV3.Render.UpsGen
