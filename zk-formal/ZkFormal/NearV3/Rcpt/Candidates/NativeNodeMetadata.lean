import ZkFormal.NearV3.Rcpt.Candidates.NodeWindowIds

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.NearV3.Render.UpsGen

theorem seed_res (tau d n v : Nat) (t : PTrie) :
    (seedNodeView tau d n v t).resOk n := by
  cases t with
  | hash h => rfl
  | leaf k s m => rfl
  | branch s cs m => rfl
  | ext k c m =>
    cases k with
    | cons a k => simp [seedNodeView,NodeS3.resOk,viewNode,viewTarget]
    | nil =>
      by_cases h : isNode c=true <;>
        simp [seedNodeView,NodeS3.resOk,viewNode,viewKid,h,viewTarget]

theorem initialized_seed_res (tau d n v : Nat) (t : PTrie) :
    (initializeMetadata n (seedNodeView tau d n v t)).resOk n := seed_res tau d n v t

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
