import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupPhysical

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render.UpsGen Assembly Qv Qv.Candidates.CombinedWalkGen

theorem nativeQueryWalks_append (pairs : List (PTrie×PTrie)) : ∀a b wa wb,
    nativeQueryWalks pairs a=some wa→nativeQueryWalks pairs b=some wb→
    nativeQueryWalks pairs (a++b)=some (wa++wb)
  | [],b,wa,wb,ha,hb=>by cases ha;exact hb
  | q::a,b,wa,wb,ha,hb=>by
    cases hq : nativeQueryWalk pairs q with
    | none=>simp [nativeQueryWalks,hq] at ha
    | some w=>
      cases ht : nativeQueryWalks pairs a with
      | none=>simp [nativeQueryWalks,hq,ht] at ha
      | some tail=>
        simp [nativeQueryWalks,hq,ht] at ha
        subst wa
        simp [nativeQueryWalks,hq,nativeQueryWalks_append pairs a b tail wb ht hb]

/-- The complete receiver/access-key/queue constructor succeeds on actual native
execution. UPS is a separate physical table sharing this inventory's rank prefix. -/
theorem native_execution_all_lookups {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (resolve : Resolve) :
    ∃v : MainValues,v.Valid ∧ v.Reads m.pre m.pre m.pre ∧ ∃ws,
      nativeQueryWalks ((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post)))
        (allLookupQueries (appliedReceipts k w) m.pre v (steps.map ImplicitStepV3.pre) resolve)=some ws := by
  obtain ⟨v,hvalid,hreads,hh,_⟩:=native_queueInputs hm hv
  have hp : (((m.pre,m.result.trie)::steps.map (fun s=>(s.pre,s.post))).map Prod.fst)=
      m.pre::steps.map ImplicitStepV3.pre := by simp [List.map_map,Function.comp_def]
  obtain ⟨queues,hq⟩:=queueLookupQueries_complete _ m.pre v (steps.map ImplicitStepV3.pre) resolve hp hh
  obtain ⟨accounts,ha,_,_⟩:=native_execution_account_lookups hm steps
  obtain ⟨accesses,hx,_,_⟩:=native_execution_access_key_lookups hm steps
  exact ⟨v,hvalid,hreads,accounts++accesses++queues,
    nativeQueryWalks_append _ _ _ _ _ (nativeQueryWalks_append _ _ _ _ _ ha hx) hq⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
