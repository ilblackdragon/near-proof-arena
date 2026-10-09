import ZkFormal.NearV3.Render.Ups.TreeNodeBytes
import ZkFormal.NearV3.Spec.TreeRecs
import ZkFormal.NearV3.Link.Records3

/-! Executable revealed-node views using exactly TreeRecs' preorder child/value IDs.
These views preserve revealed value references instead of replacing them with hashes. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

def viewSlot (vid : Nat) : Slot → NSlot3
  | .val value => .val ((u32 value.length).map UInt8.toNat) vid value.length
      ((sha256 value).map UInt8.toNat) ((sha256 value).map UInt8.toNat) false
  | .ref len hash => .ref ((u32 len).map UInt8.toNat) (hash.map UInt8.toNat)

/-- The node reached after skipping empty revealed extensions. -/
def viewTarget : Nat → PTrie → Nat
  | n, .ext [] child _ => if isNode child then viewTarget (n+1) child else n
  | n, _ => n

def viewKid (nid : Nat) (child : PTrie) : NKid :=
  if isNode child then .node nid (nodeEnc child).length (viewTarget nid child)
    (child.hashOf.map UInt8.toNat) (child.hashOf.map UInt8.toNat)
  else .hash (child.hashOf.map UInt8.toNat)

def viewKids : Nat → Kids → List NKid
  | _, .nil => []
  | n, .none rest => .none::viewKids n rest
  | n, .some child rest => viewKid n child::viewKids (n+tsize child) rest

def viewNode (nid vid : Nat) : PTrie → NodeV3
  | .hash _ => .branch none [] ((u64 0).map UInt8.toNat)
  | .leaf key value mem => .leaf key (viewSlot vid value) ((u64 mem).map UInt8.toNat)
  | .ext key child mem => .ext key (viewKid (nid+1) child) ((u64 mem).map UInt8.toNat)
  | .branch value kids mem => .branch (value.map (viewSlot vid)) (viewKids (nid+1) kids) ((u64 mem).map UInt8.toNat)

@[simp] theorem le256_toNat : ∀ bytes : Bytes, le256 (bytes.map UInt8.toNat)=leNat bytes
  | [] => rfl
  | b::rest => by simp [le256,leNat,le256_toNat rest]

@[simp] theorem viewSlot_bytes (vid : Nat) (value : Slot) (post : Bool) :
    (viewSlot vid value).bytes post=value.valueRef.map UInt8.toNat := by
  cases value <;> cases post <;> simp [viewSlot,NSlot3.bytes,Slot.valueRef]

@[simp] theorem viewKid_bytes (nid : Nat) (child : PTrie) (post : Bool) :
    (viewKid nid child).bytes post=child.hashOf.map UInt8.toNat := by
  unfold viewKid; split <;> cases post <;> rfl

@[simp] theorem viewKid_toKid (nid : Nat) (child : PTrie) :
    (viewKid nid child).toKid3=kidT nid child := by
  unfold viewKid kidT
  split <;> simp [NKid.toKid3,Link3.toB,List.map_map,Function.comp_def,UInt8.ofNat_toNat]

@[simp] theorem viewKids_toKids : ∀ nid kids,
    (viewKids nid kids).map NKid.toKid3=kidsT nid kids
  | _,.nil => rfl
  | n,.none rest => by simp [viewKids,kidsT,NKid.toKid3,viewKids_toKids n rest]
  | n,.some child rest => by simp [viewKids,kidsT,viewKids_toKids (n+tsize child) rest]

theorem viewSlot_toSlot (vid : Nat) (value : Slot) (hw : slotOk value=true) :
    (viewSlot vid value).toV3 id=vslT vid value := by
  cases value with
  | val value => rfl
  | ref len hash =>
    simp only [slotOk,Bool.and_eq_true,decide_eq_true_eq] at hw
    simp [viewSlot,NSlot3.toV3,vslT,Link3.toB,leNat_u32 hw.1,List.map_map,Function.comp_def,UInt8.ofNat_toNat]

/-- Record extraction of the revealed view is exactly the existing occurrence allocator. -/
theorem viewNode_toRec (nid vid : Nat) (t : PTrie) (hw : t.wf=true) :
    (viewNode nid vid t).toRec3 id=recT nid vid t := by
  cases t with
  | hash hash => simp [viewNode,NodeV3.toRec3,recT,leNat_u64 (by decide : 0<18446744073709551616)]
  | leaf key value mem =>
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    simp [viewNode,NodeV3.toRec3,recT,viewSlot_toSlot vid value hw.1.1.2,leNat_u64 hw.1.2]
  | ext key child mem =>
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    simp [viewNode,NodeV3.toRec3,recT,leNat_u64 hw.1.2]
  | branch value kids mem =>
    simp only [PTrie.wf,Bool.and_eq_true,decide_eq_true_eq] at hw
    simp only [viewNode,NodeV3.toRec3,recT,le256_toNat,leNat_u64 hw.2,viewKids_toKids]
    cases value with
    | none => rfl
    | some value => simp [viewSlot_toSlot vid value hw.1.1]

end ZkFormal.NearV3.Render.UpsGen
