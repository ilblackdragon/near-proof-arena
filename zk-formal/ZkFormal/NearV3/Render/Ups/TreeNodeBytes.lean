import ZkFormal.NearV3.Render.Ups.TreeNode
import ZkFormal.NearV3.Render.Ups.EdgeInsert

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

theorem runtime_bitmap_shift : ∀(cs : Kids)(i : Nat), kidsBitmap cs i=2^i*kidsBitmap cs 0
  | .nil,i => by simp [kidsBitmap]
  | .none rest,i => by
    simp only [kidsBitmap]
    rw [runtime_bitmap_shift rest (i+1),runtime_bitmap_shift rest 1,Nat.pow_succ]
    simp [Nat.mul_assoc]
  | .some c rest,i => by
    simp only [kidsBitmap]
    rw [runtime_bitmap_shift rest (i+1),runtime_bitmap_shift rest 1,Nat.pow_succ]
    simp [Nat.mul_add,Nat.mul_assoc]

@[simp] theorem treeKids_bitmap : ∀cs : Kids, kidBitmap (treeKids cs)=kidsBitmap cs 0
  | .nil => rfl
  | .none rest => by simp [treeKids,kidBitmap_cons,NKid.present,kidsBitmap,runtime_bitmap_shift rest 1,treeKids_bitmap rest]
  | .some c rest => by simp [treeKids,kidBitmap_cons,treeKid,NKid.present,kidsBitmap,runtime_bitmap_shift rest 1,treeKids_bitmap rest]

theorem map_u32_small (x : Nat) (h : x<256) : (u32 x).map UInt8.toNat=u32r x := by
  simp [u32,leN,u32r,Nat.mod_eq_of_lt h,Nat.div_eq_of_lt h]

theorem map_u16_small (x : Nat) (h : x<65536) :
    (u16 x).map UInt8.toNat=[x%256,x/256] := by
  have hh : x/256<256 := by omega
  simp [u16,leN,Nat.mod_eq_of_lt hh]

/-- The executable shallow node view serializes to the actual runtime node preimage. -/
theorem treeNode_ser {t : PTrie} {node : NodeV3} (hw : t.wf=true)
     (hn : treeNode t=some node) (post : Bool) :
    node.ser post=(nodeEnc t).map UInt8.toNat := by
  cases t with
  | hash => simp [treeNode] at hn
  | leaf key val mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp [NodeV3.ser,nodeEnc,u32Bytes,hpN]
  | ext key child mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp [NodeV3.ser,nodeEnc,u32Bytes,hpN]
  | branch value kids mem =>
    simp only [treeNode,Option.some.injEq] at hn; subst node
    simp only [PTrie.wf,Bool.and_eq_true] at hw
    have hk : Kids.wf kids 16=true := hw.1.2
    have hl := (treeKids_wf kids 16 hk).1
    have hb := Link.kidBitmap_lt hl
    rw [treeKids_bitmap] at hb
    cases value <;> simp [NodeV3.ser,nodeEnc,map_u16_small _ hb]

theorem treeNode_byte_bound {t : PTrie} {node : NodeV3} (hw : t.wf=true)
     (hn : treeNode t=some node) (post : Bool) :
    ∀b∈node.ser post,b<256 := by
  rw [treeNode_ser hw hn post]
  intro b hb
  obtain ⟨x,_,rfl⟩ := List.mem_map.1 hb
  exact UInt8.toNat_lt x

end ZkFormal.NearV3.Render.UpsGen
