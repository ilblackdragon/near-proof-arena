import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupExtensionProviders

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

/-- The extension's own requests and its recursive child requests use one
occurrence-allocated provider list, with the child's actual shifted node IDs. -/
theorem native_extension_edge_coverage (nid vid tau depth : Nat) (stored : List Nat)
    (child : PTrie) (mem : Nat) (key : List Nat) (steps : List WStep3)
    (childCoverage : ∀ss, nativeLookupSteps (nid+1) vid child (key.drop stored.length)=some ss →
      ∀s∈ss,s.mode≤1→s.e∈indexedNodeEdges (nid+1) (seedNodesT tau (depth+1) (nid+1) vid child))
    (h : nativeLookupSteps nid vid (.ext stored child mem) key=some steps) :
    ∀s∈steps,s.mode≤1→s.e∈indexedNodeEdges nid
      (seedNodesT tau depth nid vid (.ext stored child mem)) := by
  intro s hs hm
  cases hp : isPrefix stored key with
  | false=>
    simp only [nativeLookupSteps,hp,Bool.false_eq_true,ite_false] at h
    cases hr : leafLookupSteps nid vid (.ref 0 []) 0 stored key with
    | none=>simp [hr] at h
    | some raw=>
      simp only [hr,Option.map_some,Option.some.injEq] at h
      rw [←h] at hs
      apply List.mem_append_left
      exact extension_mismatch_edge_coverage nid vid tau depth stored child mem key raw hp hr s hs hm
  | true=>
    simp only [nativeLookupSteps,hp,ite_true] at h
    cases hc : nativeLookupSteps (nid+1) vid child (key.drop stored.length) with
    | none=>simp [hc] at h
    | some tail=>
      simp only [hc,Option.map_some,Option.some.injEq] at h
      rw [←h] at hs
      rcases List.mem_append.mp hs with hs|hs
      · apply List.mem_append_left
        exact extension_matched_edge_coverage nid vid tau depth stored child mem
          (nativeLookupSteps_isNode (nid+1) vid child _ tail hc) s hs
      · apply List.mem_append_right
        exact childCoverage tail hc s hs hm

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
