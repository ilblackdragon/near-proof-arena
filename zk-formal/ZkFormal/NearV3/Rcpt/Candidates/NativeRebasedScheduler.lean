import ZkFormal.NearV3.Rcpt.Candidates.NativeExecutionPayloads

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly

theorem AccountWriteRun.find_untouched {pre post : PTrie} {writes : List (List Nat×Bytes)}
    (h : AccountWriteRun pre writes post) (key : List Nat)
    (hd : ∀q∈writes.map Prod.fst,q≠key) : post.find key=pre.find key := by
  induction h with
  | nil=>rfl
  | @cons pre mid post q value rest hs ht ih=>
    rw [ih (fun q hq=>hd q (by simp [hq]))]
    exact ZkFormal.NearV3.PTrie.find_set_ne _ _ _ _ _ hs (Ne.symm (hd q (by simp)))

/-- Scheduler execution is unchanged by disjoint receipt writes except for
its concrete input and output trie payloads. -/
theorem schedStep_rebased {ctx : ApplyCtx} {pre mid oldPost final : PTrie} {so : SchedOut}
    (hs : schedStep prims ctx pre=.ok (mid,so))
    (hf : oldPost.find keyBwState=pre.find keyBwState)
    (hu : oldPost.upsert keyBwState so.state=some final) :
    schedStep prims ctx oldPost=.ok (final,so) := by
  obtain ⟨prev,p,o,hr,hp,ho,hso,_⟩:=schedStep_complete hs
  have hr' : readKey oldPost keyBwState "bandwidth scheduler state"=.ok prev := by
    simpa only [readKey,hf] using hr
  simp only [schedStep,hr',bind,Except.bind,sched_factor,hp,ho,Option.bind_some,Option.map_some,
    hso,hu,pure,Except.pure]

/-- The scheduler witness needed by UPS really executes on the old-record
post tree and reaches the unchanged native final trie with the same scheduler
output. It is not the original pre-receipt scheduler witness. -/
theorem newchunk_rebased_scheduler {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : TrieShape pre) (hwell : pre.wf=true)
    (h : applyNewChunk prims ctx pre rs=.ok out) :
    ∃writes,∃oldPost mid : PTrie,∃so : SchedOut,
      schedStep prims ctx pre=.ok (mid,so) ∧
      schedStep prims ctx oldPost=.ok (out.trie,so) ∧
      writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId) ∧
      SizedAccountRun pre writes oldPost ∧ WriteTreePair pre oldPost ∧ oldPost.wf=true ∧
      (valsOf oldPost).map List.length=(valsOf pre).map List.length := by
  obtain ⟨writes,oldPost,mid,so,hs,hkeys,hr,hpair,hpost,hlen,hfinal⟩:=
    newchunk_old_tree_reconstruct hw hwell h
  have hf:=AccountWriteRun.find_untouched hr.forget keyBwState (by
    intro q hq
    rw [hkeys] at hq
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hq
    simp [accountKeyPath,keyBwState,nibbles])
  exact ⟨writes,oldPost,mid,so,hs,schedStep_rebased hs hf hfinal,hkeys,hr,hpair,hpost,hlen⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
