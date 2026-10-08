import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountForestDigest
import ZkFormal.NearV3.Rcpt.Candidates.AcceptedNativeAccounts
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen

/-- Actual native main execution discharges all read/payload premises in the
VPOST balance for the same original/replayed forest. Exact write keys are
retained by native_rebased_physical_bounds_keys, not inferred from final roots. -/
theorem native_main_account_digest_balance {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} (hm:m.NativeValid k w)
    {writes : List (List Nat×Bytes)} {oldPost : PTrie}
    (hr:SizedAccountRun m.pre writes oldPost)
    (hkeys:writes.map Prod.fst=(appliedReceipts k w).map (fun r=>accountKeyPath r.receiverId))
    {state : Bytes} (hup:oldPost.upsert keyBwState state=some m.result.trie)
    {as : List AcctV} (has:nativeAccountViews m.pre oldPost (appliedReceipts k w)=some as)
    (steps : List ImplicitStepV3) (q : UseRequests)
    (cs : List Candidates.StoreDuplicateChain.Entry) :
    ((accountShaJobs as).map Render.digestMsg).Perm
      ((assignList q 0 (records (forestOldInputs (nativeReplayForest m steps oldPost writes))
        (Candidates.ChainMetadata.assign cs 0 (initializeList 0
          (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre)))))).flatMap postSlotDigests) := by
  have hwell:m.pre.wf=true:=by
    rw [hm.pre]
    exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.1
  obtain ⟨before,after,ha,hpre,hout⟩:=newchunk_account_context (TrieShape.of_wf _ hwell) hm.run
  have hpost:∀account,oldPost.find (accountKeyPath account)=after.1.trie.find (accountKeyPath account):=by
    intro account
    rw [hout]
    exact (ZkFormal.NearV3.find_upsert_ne (SizedAccountRun.wf hr hwell) (by decide)
      (by simp [keyBwState,accountKeyPath,nibbles]) hup).symm
  have he:=native_account_forest_digest_balance ha hr hpre hpost hkeys has
    (steps.map (fun s=>⟨s.pre,s.pre,[]⟩)) (by
      intro r hm
      obtain ⟨s,_,rfl⟩:=List.mem_map.mp hm
      rfl) q cs
  simpa only [nativeReplayForest,List.map_cons,List.map_map,Function.comp_def] using he

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
