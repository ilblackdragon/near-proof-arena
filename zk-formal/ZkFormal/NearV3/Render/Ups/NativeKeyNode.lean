import ZkFormal.NearV3.Render.Ups.NativeValueNode
import ZkFormal.NearV3.Render.Ups.TreeKeyTerminal

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

/-- Reveal child records already present in the native trie, retaining exact hashes.
The record and empty-extension resolution maps remain the store allocator's maps. -/
def nativeWalkKid (recordId resolvedId : PTrie→Nat) (child : PTrie) : NKid :=
  match child with
  | .hash hash => .hash (hash.map UInt8.toNat)
  | _ => .node (recordId child) (((treeNode child).getD default).ser false).length
      (resolvedId child) (child.hashOf.map UInt8.toNat) (child.hashOf.map UInt8.toNat)

def nativeKeyNode (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat) : PTrie→Option NodeV3
  | .hash _ => none
  | .leaf key slot mem => some (.leaf key (nativeValueSlot valueId slot) ((u64 mem).map UInt8.toNat))
  | .ext key child mem => some (.ext key (nativeWalkKid recordId resolvedId child) ((u64 mem).map UInt8.toNat))
  | .branch value kids mem => some (.branch (value.map (nativeValueSlot valueId)) (treeKids kids)
      ((u64 mem).map UInt8.toNat))

theorem nativeWalkKid_bytes (recordId resolvedId : PTrie→Nat) (child : PTrie) (post : Bool) :
    (nativeWalkKid recordId resolvedId child).bytes post=(treeKid child).bytes post := by
  cases child <;> simp [nativeWalkKid,treeKid,NKid.bytes,PTrie.hashOf]

theorem nativeKeyNode_serialization (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat)
    (source : PTrie) (post : Bool) :
    (nativeKeyNode recordId resolvedId valueId source).map (NodeV3.ser post)=
      (treeNode source).map (NodeV3.ser post) := by
  cases source with
  | hash => rfl
  | leaf key slot mem => simp [nativeKeyNode,treeNode,NodeV3.ser,nativeValueSlot_bytes]
  | ext key child mem => simp [nativeKeyNode,treeNode,NodeV3.ser,nativeWalkKid_bytes]
  | branch value kids mem => cases value <;> simp [nativeKeyNode,treeNode,NodeV3.ser,nativeValueSlot_bytes]

/-- Target of an ordinary extension-key edge at a known source key index. -/
def extKeyTarget (n i : Nat) (key : List Nat) (kid : NKid) : Nat×Nat :=
  if i+1=key.length then
    match kid with | .node _ _ res _ _ => (res,0) | _ => (n,key.length)
  else (n,i+1)

theorem ext_key_edge (n i : Nat) (s : NodeS3) (key : List Nat) (kid : NKid)
    (mem : List Nat) (hs : s.v=.ext key kid mem) (hi : i<key.length) :
    [n,i,key.getD i 0,(extKeyTarget n i key kid).1,(extKeyTarget n i key kid).2,EK_KEY]∈edgesOf3 n s := by
  by_cases hlast : i+1=key.length
  · obtain rfl|⟨front,x,rfl⟩ := List.eq_nil_or_concat key
    · simp at hi
    have he : i=front.length := by simp only [List.length_concat] at hlast; omega
    subst i
    cases kid <;> simp [extKeyTarget,edgesOf3,hs]
  · have hin : i+1<key.length := by omega
    simpa only [extKeyTarget,hlast,ite_false] using ext_inner_edge n i s key kid mem hs hin
end ZkFormal.NearV3.Render.UpsGen
