import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupExtensionCoverage
import ZkFormal.NearV3.Render.Ups.SeedWalkEdges

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

/-- Value cursor paired with the existing occurrence-based child-node cursor. -/
def lookupChildVid : Nat → Kids → Nat → Nat
  | v,.nil,_=>v
  | v,.none _,0=>v
  | v,.some _ _,0=>v
  | v,.none rest,j+1=>lookupChildVid v rest j
  | v,.some child rest,j+1=>lookupChildVid (v+(valsOf child).length) rest j

theorem nativeKidsLookupSteps_selected (parent bm hv sym nid vid : Nat) :
    ∀kids j child key,nativeChildAt kids j=some child→
    nativeKidsLookupSteps parent bm hv sym nid vid kids j key=
      (nativeLookupSteps (seedChildId nid kids j) (lookupChildVid vid kids j) child key).map
        (lookupEdge 0 sym [parent,0,sym,viewTarget (seedChildId nid kids j) child,0,EK_DOWN]::·)
  | .nil,_,_,_,h=>by simp [nativeChildAt] at h
  | .none _,0,_,_,h=>by simp [nativeChildAt] at h
  | .some c rest,0,child,key,h=>by
    simp only [nativeChildAt,Option.some.injEq] at h
    subst child;rfl
  | .none rest,j+1,child,key,h=>nativeKidsLookupSteps_selected parent bm hv sym nid vid rest j child key h
  | .some c rest,j+1,child,key,h=>
    nativeKidsLookupSteps_selected parent bm hv sym (nid+tsize c) (vid+(valsOf c).length) rest j child key h

theorem nativeKidsLookupSteps_absent (parent bm hv sym nid vid : Nat) :
    ∀kids j key,nativeChildAt kids j=none→
    nativeKidsLookupSteps parent bm hv sym nid vid kids j key=some (lookupBranchAbsent parent bm hv sym key)
  | .nil,_,_,_=>rfl
  | .none _,0,_,_=>rfl
  | .some _ _,0,_,h=>by simp [nativeChildAt] at h
  | .none rest,j+1,key,h=>nativeKidsLookupSteps_absent parent bm hv sym nid vid rest j key h
  | .some c rest,j+1,key,h=>
    nativeKidsLookupSteps_absent parent bm hv sym (nid+tsize c) (vid+(valsOf c).length) rest j key h

/-- Selecting a child preserves its exact allocated provider segment. -/
theorem indexed_child_edges (tau depth nid vid : Nat) : ∀kids j child,
    nativeChildAt kids j=some child→
    ∀e∈indexedNodeEdges (seedChildId nid kids j)
      (seedNodesT tau depth (seedChildId nid kids j) (lookupChildVid vid kids j) child),
      e∈indexedNodeEdges nid (seedKidsT tau depth nid vid kids)
  | .nil,_,_,h=>by simp [nativeChildAt] at h
  | .none _,0,_,h=>by simp [nativeChildAt] at h
  | .some c rest,0,child,h=>by
    simp only [nativeChildAt,Option.some.injEq] at h
    subst child
    intro e he
    rw [seedKidsT,indexedNodeEdges_append]
    exact List.mem_append_left _ he
  | .none rest,j+1,child,h=>indexed_child_edges tau depth nid vid rest j child h
  | .some c rest,j+1,child,h=>by
    intro e he
    have hh:=indexed_child_edges tau depth (nid+tsize c) (vid+(valsOf c).length) rest j child h e he
    rw [seedKidsT,indexedNodeEdges_append,seedNodesT_length]
    exact List.mem_append_right _ hh

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
