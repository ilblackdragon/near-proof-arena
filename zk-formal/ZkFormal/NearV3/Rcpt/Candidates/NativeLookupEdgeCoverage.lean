import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupBranchCoverage

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

mutual
/-- Every active EDGE request from an arbitrary successful native lookup is
provided by its same occurrence-allocated tree. No abstract provider premise. -/
theorem nativeLookup_edge_coverage (tau depth nid vid : Nat) : ∀tree key steps,
    nativeLookupSteps nid vid tree key=some steps→
    ∀s∈steps,s.mode≤1→s.e∈indexedNodeEdges nid (seedNodesT tau depth nid vid tree)
  | .hash _,_,_,h=>by cases h
  | .leaf stored slot mem,key,steps,h=>
    native_leaf_edge_coverage nid vid tau depth slot mem stored key steps h
  | .ext stored child mem,key,steps,h=>
    native_extension_edge_coverage nid vid tau depth stored child mem key steps
      (fun ss hs=>nativeLookup_edge_coverage tau (depth+1) (nid+1) vid child _ ss hs) h
  | .branch value kids mem,key,steps,h=>
    native_branch_edge_coverage nid vid tau depth value kids mem key steps
      (fun j child query ss hc hs=>nativeKids_selected_coverage tau (depth+1) (nid+1)
        (vid+(optSlotVal value).length) kids j child query ss hc hs) h

/-- The recursive selected-child coverage retains both compact node and value cursors. -/
theorem nativeKids_selected_coverage (tau depth nid vid : Nat) : ∀kids j child key steps,
    nativeChildAt kids j=some child→
    nativeLookupSteps (seedChildId nid kids j) (lookupChildVid vid kids j) child key=some steps→
    ∀s∈steps,s.mode≤1→s.e∈indexedNodeEdges (seedChildId nid kids j)
      (seedNodesT tau depth (seedChildId nid kids j) (lookupChildVid vid kids j) child)
  | .nil,_,_,_,_,h,_=>by simp [nativeChildAt] at h
  | .none _,0,_,_,_,h,_=>by simp [nativeChildAt] at h
  | .some c rest,0,child,key,steps,h,hs=>by
    simp only [nativeChildAt,Option.some.injEq] at h
    subst child
    exact nativeLookup_edge_coverage tau depth nid vid c key steps hs
  | .none rest,j+1,child,key,steps,h,hs=>
    nativeKids_selected_coverage tau depth nid vid rest j child key steps h hs
  | .some c rest,j+1,child,key,steps,h,hs=>
    nativeKids_selected_coverage tau depth (nid+tsize c) (vid+(valsOf c).length)
      rest j child key steps h hs
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
