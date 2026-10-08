import ZkFormal.NearV3.Rcpt.Candidates.NativeQueueLookup

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

theorem nativeQueryWalk_rows (pairs : List (PTrie×PTrie)) (q : NativeLookupQuery)
    (w : WalkR) (h : nativeQueryWalk pairs q=some w) : w.steps.length=q.key.length+2 := by
  cases hp : pairs[q.tau]? with
  | none=>simp [nativeQueryWalk,hp] at h
  | some pair=>
    obtain ⟨tree,post⟩:=pair
    dsimp only [nativeQueryWalk] at h
    rw [hp] at h
    dsimp only [Bind.bind,Option.bind] at h
    cases hs : nativeLookupSteps (forestLookupNid ((pairs.take q.tau).map Prod.fst))
      (forestLookupVid ((pairs.take q.tau).map Prod.fst)) tree q.key with
    | none=>rw [hs] at h;cases h
    | some steps=>
      rw [hs] at h
      have h := Option.some.inj h
      subst w
      exact nativeLookupWalk_length _ _ _ _ _ _ _ hs

theorem nativeQueryWalks_rows (pairs : List (PTrie×PTrie)) : ∀qs ws,
    nativeQueryWalks pairs qs=some ws→
    (ws.flatMap (·.steps)).length=(qs.map (fun q=>q.key.length+2)).sum
  | [],ws,h=>by cases h;rfl
  | q::qs,ws,h=>by
    cases hq : nativeQueryWalk pairs q with
    | none=>simp [nativeQueryWalks,hq] at h
    | some w=>
      cases ht : nativeQueryWalks pairs qs with
      | none=>simp [nativeQueryWalks,hq,ht] at h
      | some tail=>
        simp [nativeQueryWalks,hq,ht] at h
        subst ws
        simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,
          nativeQueryWalk_rows pairs q w hq,nativeQueryWalks_rows pairs qs tail ht]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
