import ZkFormal.NearV3.Render.Ups.TreeMemoryValue

/-! Memory completeness for concrete runtime terminal constructors. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

/-- Honest leaf replacement derives all carry/sign/result obligations. Remaining
metadata bounds and child bytes belong to the surrounding path allocator. -/
theorem treeRlp_memOk (I : UpsInst) (base Q : UpsPartI) (key : List Nat)
    (old : Slot) (mem : Nat) (v : Bytes)
    (he : encodeTreePart base ⟨.RLP,.leaf key old mem,newLeaf key v,0⟩=some Q)
    (hw : (PTrie.leaf key old mem).wf=true)
    (hv : I.v=v.map UInt8.toNat) (hc : I.ci<11)
    (hq : Q.qhk<2^22) (hp : Q.phk<2^22) (hL : L I<2^24)
    (hchild : ∀ b∈(child I Q).pb,b<256) : MemOk I (withMemorySign I Q) := by
  have hr := treeRlp_memory I base Q key old mem v he hv hL
  simp [encodeTreePart,treeNode,newLeaf] at he
  subst Q
  have hsrc := treeNode_wf hw rfl
  have hdst : (NodeV3.leaf key (treeSlot (.val v)) ((u64 (leafMem key v.length)).map UInt8.toNat)).wf :=
    ⟨hsrc.1,treeSlot_fresh_wf v,by simp⟩
  let e := encodePart_encoding {base with kind:=UpsRows.UKind.RLP.ix}
    (.leaf key (treeSlot old) ((u64 mem).map UInt8.toNat))
    (.leaf key (treeSlot (.val v)) ((u64 (leafMem key v.length)).map UInt8.toNat)) hdst
  apply construct_memOk I _ e (by change 2<12; decide) hc hq hp hL
    (treeNode_byte_bound hw rfl true) hchild
  · change ∀ b∈(u64 (leafMem key v.length)).map UInt8.toNat,b<256
    intro b hb; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb; exact x.toNat_lt
  · rw [memory_subtraction_scalar I _ hL]
    simp [useAV,bNV,bLV,cOV,cSV,CcV,kin,xcpV,XcpB,ind,encodePart,UpsRows.UKind.ix]
  · rw [memory_subtraction_scalar I _ hL]
    simp [useAV,bNV,bLV,cOV,cSV,CcV,kin,xcpV,XcpB,ind,encodePart,UpsRows.UKind.ix]
  · rw [← withMemorySign_RV,hr]
    change (leafMem key v.length:Int)%256^8=(le256 ((u64 (leafMem key v.length)).map UInt8.toNat):Int)
    rw [u64_memory_decode]
    omega
theorem treeRbv_memOk (I : UpsInst) (base Q : UpsPartI) (kids : Kids)
    (mem : Nat) (v : Bytes)
    (he : encodeTreePart base ⟨.RBV,.branch none kids mem,
      .branch (some (.val v)) kids (mem+valueMem v.length),0⟩=some Q)
    (hw : (PTrie.branch none kids mem).wf=true)
    (hv : I.v=v.map UInt8.toNat) (hc : I.ci<11)
    (hq : Q.qhk<2^22) (hp : Q.phk<2^22) (hL : L I<2^24)
    (hchild : ∀ b∈(child I Q).pb,b<256) : MemOk I (withMemorySign I Q) := by
  have hr := treeRbv_memory I base Q kids mem v he hw hv hL
  have hm := encoded_source_memory_exact he hw
  change pfx (memRb Q) 8=(mem:Int) at hm
  have hmb := source_memory_bound (.branch none kids mem) hw
  change mem<256^8 at hmb
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hw rfl
  have hdst : (NodeV3.branch (some (treeSlot (.val v))) (treeKids kids)
      ((u64 (mem+valueMem v.length)).map UInt8.toNat)).wf :=
    ⟨hsrc.1,by intro x hx; cases hx; exact treeSlot_fresh_wf v,hsrc.2.2.1,by simp⟩
  let e := encodePart_encoding {base with kind:=UpsRows.UKind.RBV.ix}
    (.branch none (treeKids kids) ((u64 mem).map UInt8.toNat))
    (.branch (some (treeSlot (.val v))) (treeKids kids)
      ((u64 (mem+valueMem v.length)).map UInt8.toNat)) hdst
  apply construct_memOk I _ e (by change 4<12; decide) hc hq hp hL
    (treeNode_byte_bound hw rfl true) hchild
  · change ∀ b∈(u64 (mem+valueMem v.length)).map UInt8.toNat,b<256
    intro b hb; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb; exact x.toNat_lt
  · rw [memory_subtraction_scalar I _ hL]
    simp [useAV,bNV,bLV,cOV,cSV,CcV,kin,xcpV,XcpB,ind,encodePart,UpsRows.UKind.ix] at hm ⊢
    omega
  · rw [memory_subtraction_scalar I _ hL]
    simp [useAV,bNV,bLV,cOV,cSV,CcV,kin,xcpV,XcpB,ind,encodePart,UpsRows.UKind.ix] at hm ⊢
    omega
  · rw [← withMemorySign_RV,hr]
    change ((mem+valueMem v.length:Nat):Int)%256^8=
      (le256 ((u64 (mem+valueMem v.length)).map UInt8.toNat):Int)
    rw [u64_memory_decode]
    omega
theorem treeRbr_memOk (I : UpsInst) (base Q : UpsPartI) (old : Slot) (kids : Kids)
    (mem : Nat) (v : Bytes)
    (he : encodeTreePart base ⟨.RBR,.branch (some old) kids mem,
      .branch (some (.val v)) kids (mem+valueMem v.length-valueMem old.len),0⟩=some Q)
    (hw : (PTrie.branch (some old) kids mem).wf=true)
    (hv : I.v=v.map UInt8.toNat) (hc : I.ci<11)
    (hq : Q.qhk<2^22) (hp : Q.phk<2^22) (hL : L I<2^24)
    (hchild : ∀ b∈(child I Q).pb,b<256) : MemOk I (withMemorySign I Q) := by
  have hr := treeRbr_memory I base Q old kids mem v he hw hv hL
  have hs := treeRbr_slot_scalar base Q old kids mem v he hw
  have hold : old.len<256^4 := by
    have hw0 := hw
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw0
    have hh := hw0.1.1
    cases old <;> simp_all [slotOk,Slot.len]
  have hm := encoded_source_memory_exact he hw
  change pfx (memRb Q) 8=(mem:Int) at hm
  have hmb := source_memory_bound (.branch (some old) kids mem) hw
  change mem<256^8 at hmb
  simp [encodeTreePart,treeNode] at he
  subst Q
  have hsrc := treeNode_wf hw rfl
  have hdst : (NodeV3.branch (some (treeSlot (.val v))) (treeKids kids)
      ((u64 (mem+valueMem v.length-valueMem old.len)).map UInt8.toNat)).wf :=
    ⟨hsrc.1,by intro x hx; cases hx; exact treeSlot_fresh_wf v,hsrc.2.2.1,by simp⟩
  let e := encodePart_encoding {base with kind:=UpsRows.UKind.RBR.ix}
    (.branch (some (treeSlot old)) (treeKids kids) ((u64 mem).map UInt8.toNat))
    (.branch (some (treeSlot (.val v))) (treeKids kids)
      ((u64 (mem+valueMem v.length-valueMem old.len)).map UInt8.toNat)) hdst
  apply construct_memOk I _ e (by change 3<12; decide) hc hq hp hL
    (treeNode_byte_bound hw rfl true) hchild
  · change ∀ b∈(u64 (mem+valueMem v.length-valueMem old.len)).map UInt8.toNat,b<256
    intro b hb; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb; exact x.toNat_lt
  · rw [memory_subtraction_scalar I _ hL]
    simp [useAV,bNV,bLV,cOV,cSV,CcV,kin,xcpV,XcpB,ind,encodePart,UpsRows.UKind.ix] at hm hs ⊢
    omega
  · rw [memory_subtraction_scalar I _ hL]
    simp [useAV,bNV,bLV,cOV,cSV,CcV,kin,xcpV,XcpB,ind,encodePart,UpsRows.UKind.ix] at hm hs ⊢
    omega
  · rw [← withMemorySign_RV,hr]
    change ((mem+valueMem v.length-valueMem old.len:Nat):Int)%256^8=
      (le256 ((u64 (mem+valueMem v.length-valueMem old.len)).map UInt8.toNat):Int)
    rw [u64_memory_decode]
    omega
end ZkFormal.NearV3.Render.UpsGen
