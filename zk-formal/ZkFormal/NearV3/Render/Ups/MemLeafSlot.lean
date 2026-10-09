import ZkFormal.NearV3.Render.Ups.MemSlotScalar

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

theorem encoded_leaf_slot (base : UpsPartI) (key : List Nat) (value : Slot)
    (mem : Nat) (dst : NodeV3) (hw : slotOk value=true) :
    pfx (slb (encodePart base (.leaf key (treeSlot value) ((u64 mem).map UInt8.toNat)) dst)) 8=
      (value.len:Int) := by
  have hlen : value.len<256^4 := by cases value <;> simp_all [slotOk,Slot.len]
  cases value with
  | val value =>
    apply slot_memory_scalar _
      ([0]++u32Bytes (hpN key true).length++hpN key true)
      ((sha256 value).map UInt8.toNat++(u64 mem).map UInt8.toNat) value.length _ _ hlen
    · simp [encodePart,NodeV3.ser,treeSlot,NSlot3.bytes,List.append_assoc]
    · simp [encodePart,valueOffset,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,
        u32Bytes,hpN,Render.NodeInfo.hexPrefix_len] <;> omega
  | ref len hash =>
    apply slot_memory_scalar _
      ([0]++u32Bytes (hpN key true).length++hpN key true)
      (hash.map UInt8.toNat++(u64 mem).map UInt8.toNat) len _ _ hlen
    · simp [encodePart,NodeV3.ser,treeSlot,NSlot3.bytes,List.append_assoc]
    · simp [encodePart,valueOffset,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,
        u32Bytes,hpN,Render.NodeInfo.hexPrefix_len] <;> omega
end ZkFormal.NearV3.Render.UpsGen
