import ZkFormal.NearV3.Render.Ups.NativeKeyEdge

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

/-- Shallow child annotations use the supplied global record and resolution maps. -/
def nativeWalkKids (recordId resolvedId : PTrie→Nat) : Kids→List NKid
  | .nil => []
  | .none rest => .none::nativeWalkKids recordId resolvedId rest
  | .some child rest => nativeWalkKid recordId resolvedId child::nativeWalkKids recordId resolvedId rest

def nativePathNode (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat) : PTrie→Option NodeV3
  | .branch value kids mem => some (.branch (value.map (nativeValueSlot valueId))
      (nativeWalkKids recordId resolvedId kids) ((u64 mem).map UInt8.toNat))
  | t => nativeKeyNode recordId resolvedId valueId t

theorem nativeWalkKid_present (recordId resolvedId : PTrie→Nat) (child : PTrie) :
    (nativeWalkKid recordId resolvedId child).present=true := by
  cases child <;> rfl

theorem nativeWalkKids_bytes (recordId resolvedId : PTrie→Nat) : ∀ kids post,
    (nativeWalkKids recordId resolvedId kids).flatMap (NKid.bytes post)=
      (treeKids kids).flatMap (NKid.bytes post)
  | .nil,_ => rfl
  | .none rest,post => by simp [nativeWalkKids,treeKids,NKid.bytes,nativeWalkKids_bytes recordId resolvedId rest post]
  | .some child rest,post => by
    simp [nativeWalkKids,treeKids,nativeWalkKid_bytes,nativeWalkKids_bytes recordId resolvedId rest post]

theorem nativeWalkKids_bitmap (recordId resolvedId : PTrie→Nat) : ∀ kids,
    kidBitmap (nativeWalkKids recordId resolvedId kids)=kidBitmap (treeKids kids)
  | .nil => rfl
  | .none rest => by
    simp [nativeWalkKids,treeKids,kidBitmap_cons,nativeWalkKids_bitmap recordId resolvedId rest]
  | .some child rest => by
    cases child <;> simp [nativeWalkKids,treeKids,kidBitmap_cons,nativeWalkKid,treeKid,NKid.present,
      nativeWalkKids_bitmap recordId resolvedId rest]

/-- Annotating all native children and values leaves both serialized snapshots intact. -/
theorem nativePathNode_serialization (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat)
    (source : PTrie) (post : Bool) :
    (nativePathNode recordId resolvedId valueId source).map (NodeV3.ser post)=
      (treeNode source).map (NodeV3.ser post) := by
  cases source with
  | hash => rfl
  | leaf key slot mem => exact nativeKeyNode_serialization recordId resolvedId valueId (.leaf key slot mem) post
  | ext key child mem => exact nativeKeyNode_serialization recordId resolvedId valueId (.ext key child mem) post
  | branch value kids mem =>
    cases value <;> simp [nativePathNode,treeNode,NodeV3.ser,nativeValueSlot_bytes,
      nativeWalkKids_bytes,nativeWalkKids_bitmap]

/-- Child-ID annotation preserves the native indexed child lookup. -/
theorem nativeWalkKids_get (recordId resolvedId : PTrie→Nat) : ∀ kids n child,
    nativeChildAt kids n=some child →
    (nativeWalkKids recordId resolvedId kids)[n]?=some (nativeWalkKid recordId resolvedId child)
  | .nil,_,_,h => by simp [nativeChildAt] at h
  | .none _,0,_,h => by simp [nativeChildAt] at h
  | .some c _,0,child,h => by
    simp only [nativeChildAt,Option.some.injEq] at h
    subst child; rfl
  | .none rest,n+1,child,h => nativeWalkKids_get recordId resolvedId rest n child h
  | .some c rest,n+1,child,h => nativeWalkKids_get recordId resolvedId rest n child h
end ZkFormal.NearV3.Render.UpsGen
