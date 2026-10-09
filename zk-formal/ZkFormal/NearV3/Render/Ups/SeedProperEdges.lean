import ZkFormal.NearV3.Render.Ups.SeedTerminalEdges
import ZkFormal.NearV3.Render.Ups.NativeProperEdges

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec UpsRows ZkFormal.Near

/-- Selected-child occurrence agreement. Other children need no correspondence
with the trace-local record map. -/
def SeedProperTarget (n : Nat) (resolvedId : PTrie→Nat) (p : TreePart) : Prop :=
  match p.source with
  | .branch _ kids _ => ∀ child, nativeChildAt kids p.slot=some child →
      resolvedId child=viewTarget (seedChildId (n+1) kids p.slot) child
  | .ext _ child _ => resolvedId child=viewTarget (n+1) child
  | _ => True

/-- Every proper native ancestor edge is supplied by its concrete occurrence seed,
using only the selected child's allocated target, not a global subtree-ID map. -/
theorem seed_proper_edge (recordId resolvedId : PTrie→Nat)
    {root : PTrie} {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root key value=some run) (p : TreePart) (hp : p∈run.parts)
    (hd : descendKind p.kind=true) (i : Nat) (hi : i<(partWalkKey p).length)
    (tau depth vid : Nat) (ht : SeedProperTarget (recordId p.source) resolvedId p) :
    partWalkEdge recordId resolvedId p i∈edgesOf3 (recordId p.source)
      (seedNodeView tau depth (recordId p.source) vid p.source) := by
  have hs := traceUpsert_properSources root key value run hr p hp
  cases hk : p.kind <;> simp only [hk,descendKind] at hd
  all_goals try contradiction
  · obtain ⟨value,kids,mem,child,cm,hsrc,hchild,hmem⟩ := (show ∃ value kids mem child cm,
      p.source=.branch value kids mem ∧ nativeChildAt kids p.slot=some child ∧ child.mem?=some cm by
        simpa only [ProperSource,hk] using hs)
    have hiz : i=0 := by simp only [partWalkKey,hk,List.length_singleton] at hi; omega
    subst i
    have hn : isNode child=true := by cases child <;> simp_all [PTrie.mem?,isNode]
    have htf : ∀ c, nativeChildAt kids p.slot=some c →
        resolvedId c=viewTarget (seedChildId (recordId p.source+1) kids p.slot) c := by
      simpa only [SeedProperTarget,hsrc] using ht
    have ht' := htf child hchild
    have he := seed_branch_child tau depth (recordId p.source) vid p.slot value kids mem child hchild hn
    simpa [partWalkEdge,partWalkTarget,partWalkKey,hk,sourcePathChild,hsrc,hchild,ht'] using he
  · obtain ⟨key,child,mem,cm,hsrc,_,hmem⟩ := (show ∃ key child mem cm,
      p.source=.ext key child mem ∧ key≠[] ∧ child.mem?=some cm by
        simpa only [ProperSource,hk] using hs)
    have hi' : i<key.length := by simpa only [partWalkKey,hk,hsrc] using hi
    have ht' : resolvedId child=viewTarget (recordId p.source+1) child := by
      simpa only [SeedProperTarget,hsrc] using ht
    have he := seed_ext_key tau depth (recordId p.source) vid i key child mem hi'
    have hn : isNode child=true := by cases child <;> simp_all [PTrie.mem?,isNode]
    simpa [partWalkEdge,partWalkTarget,partWalkKey,hk,sourcePathChild,hsrc,
      extKeyTarget,viewKid,hn,ht'] using he
end ZkFormal.NearV3.Render.UpsGen
