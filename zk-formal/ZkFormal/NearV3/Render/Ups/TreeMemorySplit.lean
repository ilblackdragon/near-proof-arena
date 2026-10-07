import ZkFormal.NearV3.Render.Ups.MemSplitScalars
import ZkFormal.NearV3.Render.Ups.MemLeafSlot

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

theorem treeSpbFreshSome_memory (I : UpsInst) (base Q : UpsPartI) (source child : PTrie)
    (v : Bytes) (slot : Nat) (hi : I.ci=5 ∨ I.ci=7)
    (he : encodeTreePart base ⟨.SPB,source,.branch (some (.val v)) (kids1 slot child)
      (50+valueMem v.length+child.memD),0⟩=some Q)
    (hm : Q.mB=child.memD) (hv : I.v=v.map UInt8.toNat) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((50+valueMem v.length+child.memD:Nat):Int) := by
  rw [spb_fresh_some_memory_scalar I Q hL (encodeTreePart_kind he) hi,hm]
  simp [valueMem,L,hv]
  omega

theorem treeSpbFreshNone_memory (I : UpsInst) (base Q : UpsPartI) (source old : PTrie)
    (key : List Nat) (v : Bytes) (x y : Nat) (hi : I.ci=6 ∨ I.ci=9)
    (he : encodeTreePart base ⟨.SPB,source,.branch none (kids2 x old y (newLeaf key v))
      (50+old.memD+leafMem key v.length),0⟩=some Q)
    (hm : Q.mB=old.memD) (hk : key.length≤1)
    (hv : I.v=v.map UInt8.toNat) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((50+old.memD+leafMem key v.length:Nat):Int) := by
  rw [spb_fresh_none_memory_scalar I Q hL (encodeTreePart_kind he) hi,hm]
  simp [leafMem,Render.NodeInfo.hexPrefix_len,L,hv]
  omega

theorem treeSpbValue_memory (I : UpsInst) (base Q : UpsPartI) (oldKey key : List Nat)
    (value : Slot) (mem slot : Nat) (v : Bytes) (hi : I.ci=4)
    (he : encodeTreePart base ⟨.SPB,.leaf oldKey value mem,
      .branch (some value) (kids1 slot (newLeaf key v))
        (50+valueMem value.len+leafMem key v.length),0⟩=some Q)
    (hw : (PTrie.leaf oldKey value mem).wf=true) (hk : key.length≤1)
    (hv : I.v=v.map UInt8.toNat) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((50+valueMem value.len+leafMem key v.length:Nat):Int) := by
  have hkind := encodeTreePart_kind he
  have hs : pfx (slb Q) 8=(value.len:Int) := by
    simp [encodeTreePart,treeNode] at he
    subst Q
    apply encoded_leaf_slot
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    exact hw.1.1.2
  rw [spb_value_memory_scalar I Q hL hkind hi value.len hs]
  simp [leafMem,valueMem,Render.NodeInfo.hexPrefix_len,L,hv]
  omega

theorem treeSpbChildSome_memory (I : UpsInst) (base Q : UpsPartI) (key : List Nat)
    (child : PTrie) (mem slot : Nat) (v : Bytes) (hi : I.ci=8)
    (he : encodeTreePart base ⟨.SPB,.ext key child mem,
      .branch (some (.val v)) (kids1 slot child)
        (50+valueMem v.length+(mem-extOwnMem key)),0⟩=some Q)
    (hw : (PTrie.ext key child mem).wf=true)
    (hv : I.v=v.map UInt8.toNat) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((50+valueMem v.length+(mem-extOwnMem key):Nat):Int) := by
  have hm := encoded_source_memory_exact he hw
  rw [spb_child_some_memory_scalar I Q hL (encodeTreePart_kind he) hi mem hm]
  simp [encodeTreePart,treeNode] at he
  subst Q
  simp [encodePart,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,extOwnMem,valueMem,
    Render.NodeInfo.hexPrefix_len,L,hv]
  omega

theorem treeSpbChildNone_memory (I : UpsInst) (base Q : UpsPartI) (oldKey key : List Nat)
    (child : PTrie) (mem x y : Nat) (v : Bytes) (hi : I.ci=10)
    (he : encodeTreePart base ⟨.SPB,.ext oldKey child mem,
      .branch none (kids2 x child y (newLeaf key v))
        (50+(mem-extOwnMem oldKey)+leafMem key v.length),0⟩=some Q)
    (hw : (PTrie.ext oldKey child mem).wf=true) (hk : key.length≤1)
    (hv : I.v=v.map UInt8.toNat) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((50+(mem-extOwnMem oldKey)+leafMem key v.length:Nat):Int) := by
  have hm := encoded_source_memory_exact he hw
  rw [spb_child_none_memory_scalar I Q hL (encodeTreePart_kind he) hi mem hm]
  simp [encodeTreePart,treeNode] at he
  subst Q
  simp [encodePart,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,extOwnMem,leafMem,
    Render.NodeInfo.hexPrefix_len,L,hv]
  omega
end ZkFormal.NearV3.Render.UpsGen
