import ZkFormal.NearV3.Render.Ups.MemPrefixScalars
import ZkFormal.NearV3.Render.Ups.MemSlotScalar

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

theorem treeNlf_memory (I : UpsInst) (base Q : UpsPartI) (source : PTrie)
    (key : List Nat) (v : Bytes)
    (he : encodeTreePart base ⟨.NLF,source,newLeaf key v,0⟩=some Q)
    (hk : key.length≤1) (hv : I.v=v.map UInt8.toNat) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=(leafMem key v.length:Int) := by
  rw [nlf_memory_scalar I Q hL (encodeTreePart_kind he)]
  simp [leafMem,Render.NodeInfo.hexPrefix_len,L,hv]
  omega

theorem treeRbi_memory (I : UpsInst) (base Q : UpsPartI) (value : Option Slot)
    (oldKids newKids : Kids) (mem slot : Nat) (key : List Nat) (v : Bytes)
    (he : encodeTreePart base ⟨.RBI,.branch value oldKids mem,
      .branch value newKids (mem+leafMem key v.length),slot⟩=some Q)
    (hw : (PTrie.branch value oldKids mem).wf=true)
    (hk : key.length≤1) (hv : I.v=v.map UInt8.toNat) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((mem+leafMem key v.length:Nat):Int) := by
  have hm := encoded_source_memory_exact he hw
  rw [rbi_memory_scalar I Q hL (encodeTreePart_kind he) mem hm]
  simp [leafMem,Render.NodeInfo.hexPrefix_len,L,hv]
  omega

theorem treeMve_memory (I : UpsInst) (base Q : UpsPartI) (oldKey newKey : List Nat)
    (child : PTrie) (mem : Nat)
    (he : encodeTreePart base ⟨.MVE,.ext oldKey child mem,
      .ext newKey child (extOwnMem newKey+(mem-extOwnMem oldKey)),0⟩=some Q)
    (hw : (PTrie.ext oldKey child mem).wf=true) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((extOwnMem newKey+(mem-extOwnMem oldKey):Nat):Int) := by
  have hm := encoded_source_memory_exact he hw
  rw [mve_memory_scalar I Q hL (encodeTreePart_kind he) mem hm]
  simp [encodeTreePart,treeNode] at he
  subst Q
  simp [encodePart,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,extOwnMem,Render.NodeInfo.hexPrefix_len] <;> omega

theorem treeWex_memory (I : UpsInst) (base Q : UpsPartI) (source child : PTrie)
    (key : List Nat)
    (he : encodeTreePart base ⟨.WEX,source,.ext key child (extOwnMem key+child.memD),0⟩=some Q)
    (hm : Q.mB=child.memD) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((extOwnMem key+child.memD:Nat):Int) := by
  rw [wex_memory_scalar I Q hL (encodeTreePart_kind he),hm]
  cases hs : treeNode source with
  | none => simp [encodeTreePart,hs] at he
  | some src =>
    unfold encodeTreePart at he
    rw [hs] at he
    simp [treeNode] at he
    subst Q
    simp [encodePart,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,extOwnMem,Render.NodeInfo.hexPrefix_len] <;> omega
theorem treeMvl_memory (I : UpsInst) (base Q : UpsPartI) (oldKey newKey : List Nat)
    (value : Slot) (mem : Nat)
    (he : encodeTreePart base ⟨.MVL,.leaf oldKey value mem,
      .leaf newKey value (leafMem newKey value.len),0⟩=some Q)
    (hw : (PTrie.leaf oldKey value mem).wf=true) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=(leafMem newKey value.len:Int) := by
  have hk := encodeTreePart_kind he
  have hs : pfx (slb Q) 8=(value.len:Int) := by
    simp [encodeTreePart,treeNode] at he
    subst Q
    have hlen : value.len<256^4 := by
      simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
      have hh := hw.1.1.2
      cases value <;> simp_all [slotOk,Slot.len]
    cases value with
    | val value =>
      apply slot_memory_scalar _
        ([0]++u32Bytes (hpN oldKey true).length++hpN oldKey true)
        ((sha256 value).map UInt8.toNat++(u64 mem).map UInt8.toNat) value.length _ _ hlen
      · simp [encodePart,NodeV3.ser,treeSlot,NSlot3.bytes,List.append_assoc]
      · simp [encodePart,valueOffset,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,
          u32Bytes,hpN,Render.NodeInfo.hexPrefix_len] <;> omega
    | ref len hash =>
      apply slot_memory_scalar _
        ([0]++u32Bytes (hpN oldKey true).length++hpN oldKey true)
        (hash.map UInt8.toNat++(u64 mem).map UInt8.toNat) len _ _ hlen
      · simp [encodePart,NodeV3.ser,treeSlot,NSlot3.bytes,List.append_assoc]
      · simp [encodePart,valueOffset,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,
          u32Bytes,hpN,Render.NodeInfo.hexPrefix_len] <;> omega
  rw [mvl_memory_scalar I Q hL hk value.len hs]
  simp [encodeTreePart,treeNode] at he
  subst Q
  simp [encodePart,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,leafMem,Render.NodeInfo.hexPrefix_len]
  omega
end ZkFormal.NearV3.Render.UpsGen
