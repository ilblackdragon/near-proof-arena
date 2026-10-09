import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueryList

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

theorem nativeQueryWalk_complete (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery)
    (tree post : PTrie) (value : Option Bytes) (hp : pairs[q.tau]?=some (tree,post))
    (hf : tree.find q.key=some value) : ∃w,nativeQueryWalk pairs q=some w := by
  have hd:=nativeLookupSteps_defined (forestLookupNid ((pairs.take q.tau).map Prod.fst))
    (forestLookupVid ((pairs.take q.tau).map Prod.fst)) tree q.key
  rw [hf] at hd
  cases hs : nativeLookupSteps (forestLookupNid ((pairs.take q.tau).map Prod.fst))
    (forestLookupVid ((pairs.take q.tau).map Prod.fst)) tree q.key with
  | none=>rw [hs] at hd;cases hd
  | some steps=>
    refine ⟨nativeLookupWalk q.wid q.tau (forestLookupNid ((pairs.take q.tau).map Prod.fst)) tree steps,?_⟩
    dsimp only [nativeQueryWalk]
    rw [hp]
    dsimp only [Bind.bind,Option.bind]
    rw [hs]
    rfl

theorem nativeQueryWalks_complete (pairs : List (PTrie×PTrie)) : ∀qs,
    (∀q∈qs,∃w,nativeQueryWalk pairs q=some w)→∃ws,nativeQueryWalks pairs qs=some ws
  | [],_=>⟨[],rfl⟩
  | q::qs,h=>by
    obtain ⟨w,hw⟩:=h q (by simp)
    obtain ⟨ws,hws⟩:=nativeQueryWalks_complete pairs qs (fun q hq=>h q (by simp [hq]))
    exact ⟨w::ws,by simp [nativeQueryWalks,hw,hws]⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
