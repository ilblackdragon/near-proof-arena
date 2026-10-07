import ZkFormal.NearV3.Render.Ups.MemValueScalars

/-! Actual terminal executions determine their exact memory scalar before u64 serialization. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

theorem treeRlp_memory (I : UpsInst) (base Q : UpsPartI) (key : List Nat)
    (old : Slot) (mem : Nat) (v : Bytes)
    (he : encodeTreePart base ⟨.RLP,.leaf key old mem,newLeaf key v,0⟩=some Q)
    (hv : I.v=v.map UInt8.toNat) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=(leafMem key v.length:Int) := by
  have hk := encodeTreePart_kind he
  have hr := rlp_memory_scalar I Q hL hk
  rw [hr]
  simp [encodeTreePart,treeNode,newLeaf] at he
  subst Q
  simp [encodePart,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,hpN,leafMem,L,hv,Render.NodeInfo.hexPrefix_len]
  omega

theorem treeRbv_memory (I : UpsInst) (base Q : UpsPartI) (kids : Kids)
    (mem : Nat) (v : Bytes)
    (he : encodeTreePart base ⟨.RBV,.branch none kids mem,
      .branch (some (.val v)) kids (mem+valueMem v.length),0⟩=some Q)
    (hw : (PTrie.branch none kids mem).wf=true)
    (hv : I.v=v.map UInt8.toNat) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((mem+valueMem v.length:Nat):Int) := by
  have hm := encoded_source_memory_exact he hw
  have hk := encodeTreePart_kind he
  have hr := rbv_memory_scalar I Q hL hk mem hm
  rw [hr]
  simp [valueMem,L,hv]
  omega
theorem branch_slot_scalar (Q : UpsPartI) (n : Nat) (rest : List Nat)
    (hb : Q.pb=[2]++(u32 n).map UInt8.toNat++rest) (ho : Q.soff=1) (hn : n<256^4) :
    pfx (slb Q) 8=(n:Int) := by
  simp [pfx,slb,hb,ho,UpsRows.toNats_u32,List.getD]
  omega

theorem treeRbr_memory (I : UpsInst) (base Q : UpsPartI) (old : Slot) (kids : Kids)
    (mem : Nat) (v : Bytes)
    (he : encodeTreePart base ⟨.RBR,.branch (some old) kids mem,
      .branch (some (.val v)) kids (mem+valueMem v.length-valueMem old.len),0⟩=some Q)
    (hw : (PTrie.branch (some old) kids mem).wf=true)
    (hv : I.v=v.map UInt8.toNat) (hL : L I<2^24) :
    RV I (withMemorySign I Q)=((mem+valueMem v.length-valueMem old.len:Nat):Int) := by
  have hm := encoded_source_memory_exact he hw
  have hk := encodeTreePart_kind he
  have hs : pfx (slb Q) 8=(old.len:Int) := by
    simp [encodeTreePart,treeNode] at he
    subst Q
    have hold : slotOk old=true := by
      simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
      exact hw.1.1
    have hlen : old.len<256^4 := by cases old <;> simp_all [slotOk,Slot.len]
    cases old with
    | val value =>
      apply branch_slot_scalar _ value.length
        ((sha256 value).map UInt8.toNat ++ [kidBitmap (treeKids kids)%256,kidBitmap (treeKids kids)/256] ++
          (treeKids kids).flatMap (NKid.bytes true) ++ (u64 mem).map UInt8.toNat) _ rfl hlen
      simp [encodePart,NodeV3.ser,treeSlot,NSlot3.bytes,List.append_assoc]
    | ref len hash =>
      apply branch_slot_scalar _ len
        (hash.map UInt8.toNat ++ [kidBitmap (treeKids kids)%256,kidBitmap (treeKids kids)/256] ++
          (treeKids kids).flatMap (NKid.bytes true) ++ (u64 mem).map UInt8.toNat) _ rfl hlen
      simp [encodePart,NodeV3.ser,treeSlot,NSlot3.bytes,List.append_assoc]
  rw [rbr_memory_scalar I Q hL hk mem old.len hm hs]
  simp only [valueMem,L,hv,List.length_map]
  omega

end ZkFormal.NearV3.Render.UpsGen
