import ZkFormal.NearV3.Render.Ups.TreeProperSources

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

/-- At the final ancestor nibble enter its resolved child; otherwise stay in the source. -/
def partWalkTarget (recordId resolvedId : PTrie→Nat) (p : TreePart) (i : Nat) : Nat×Nat :=
  if i+1=(partWalkKey p).length then
    match sourcePathChild p with
    | some child => (resolvedId child,0)
    | none => (recordId p.source,i+1)
  else (recordId p.source,i+1)

def partWalkEdge (recordId resolvedId : PTrie→Nat) (p : TreePart) (i : Nat) : List Nat :=
  [recordId p.source,i,(partWalkKey p).getD i 0,(partWalkTarget recordId resolvedId p i).1,
    (partWalkTarget recordId resolvedId p i).2,if p.kind=.RDB then EK_DOWN else EK_KEY]

/-- Every actual proper ancestor segment has at least one consumed nibble. -/
theorem properSource_walkKey_nonempty {p : TreePart} (hp : ProperSource p)
    (hd : descendKind p.kind=true) : (partWalkKey p)≠[] := by
  cases hk : p.kind <;> simp only [hk,descendKind] at hd
  all_goals try contradiction
  · simp [partWalkKey,hk]
  · obtain ⟨key,child,mem,cm,hs,hne,_⟩ := (show ∃ key child mem cm,
      p.source=.ext key child mem ∧ key≠[] ∧ child.mem?=some cm by simpa [ProperSource,hk] using hp)
    simpa [partWalkKey,hk,hs] using hne

/-- The executable native source annotation provides every edge of every actual proper
ancestor segment. No edge-membership premise or source memory bound is supplied. -/
theorem nativePathNode_proper_edge (recordId resolvedId : PTrie→Nat) (valueId : Slot→Nat)
    {root : PTrie} {key : List Nat} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root key v=some run) (p : TreePart) (hp : p∈run.parts)
    (hd : descendKind p.kind=true) (i : Nat) (hi : i<(partWalkKey p).length) (s : NodeS3)
    (hnode : nativePathNode recordId resolvedId valueId p.source=some s.v) :
    partWalkEdge recordId resolvedId p i∈edgesOf3 (recordId p.source) s := by
  have hs := traceUpsert_properSources root key v run hr p hp
  cases hk : p.kind <;> simp only [hk,descendKind] at hd
  all_goals try contradiction
  · have hshape : ∃ value kids mem child cm,p.source=.branch value kids mem ∧
        nativeChildAt kids p.slot=some child ∧ child.mem?=some cm := by
      simpa only [ProperSource,hk] using hs
    obtain ⟨value,kids,mem,child,cm,hsrc,hchild,hmem⟩ := hshape
    have hiz : i=0 := by simp only [partWalkKey,hk,List.length_singleton] at hi; omega
    subst i
    have he := nativePathNode_child_edge recordId resolvedId valueId (recordId p.source) p.slot s
      value kids mem child cm hchild hmem (by simpa only [hsrc] using hnode)
    simpa [partWalkEdge,partWalkTarget,partWalkKey,hk,sourcePathChild,hsrc,hchild] using he
  · have hshape : ∃ key child mem cm,p.source=.ext key child mem ∧ key≠[] ∧ child.mem?=some cm := by
      simpa only [ProperSource,hk] using hs
    obtain ⟨key,child,mem,cm,hsrc,_,hmem⟩ := hshape
    have hv : s.v=.ext key (nativeWalkKid recordId resolvedId child) ((u64 mem).map UInt8.toNat) := by
      simpa only [hsrc,nativePathNode,nativeKeyNode,Option.some.injEq] using hnode.symm
    have hi' : i<key.length := by simpa only [partWalkKey,hk,hsrc] using hi
    have he := ext_key_edge (recordId p.source) i s key _ _ hv hi'
    have ht : partWalkTarget recordId resolvedId p i=
        extKeyTarget (recordId p.source) i key (nativeWalkKid recordId resolvedId child) := by
      cases child with
      | hash => simp [PTrie.mem?] at hmem
      | leaf | ext | branch => simp [partWalkTarget,partWalkKey,hk,hsrc,sourcePathChild,extKeyTarget,nativeWalkKid]
    simpa only [partWalkEdge,ht,partWalkKey,hk,hsrc,reduceCtorEq,ite_false] using he
end ZkFormal.NearV3.Render.UpsGen
