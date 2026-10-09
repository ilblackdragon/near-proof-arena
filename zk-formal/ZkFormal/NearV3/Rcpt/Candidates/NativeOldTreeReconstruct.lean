import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayUpsert

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0 Assembly

/-- Reconstruct the exact final native trie by applying the scheduler upsert
last to the shape-preserving old-record tree containing all receipt writes. -/
theorem newchunk_old_tree_reconstruct {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : TrieShape pre) (hwell : pre.wf=true)
    (h : applyNewChunk prims ctx pre rs=.ok out) :
    ∃writes,∃oldPost mid : PTrie,∃so : SchedOut,
      schedStep prims ctx pre=.ok (mid,so) ∧
      writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId) ∧
      SizedAccountRun pre writes oldPost ∧ WriteTreePair pre oldPost ∧ oldPost.wf=true ∧
      (ZkFormal.NearV3.valsOf oldPost).map List.length=(ZkFormal.NearV3.valsOf pre).map List.length ∧
      oldPost.upsert keyBwState so.state=some out.trie := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨⟨mid,so⟩,hsched,h⟩:=bind_ok' h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨after,ha,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  have hout : after.1.trie=out.trie := by
    cases h
    rfl
  obtain ⟨writes,hwrite,hkeys⟩:=native_sized_account_writes ctx rs 0 _ after ha
  obtain ⟨oldPost,hreplay,hreads⟩:=SizedAccountRun.rebase hwrite
    (fun key=>∃account,key=accountKeyPath account) (by
      intro key hk
      rw [hkeys] at hk
      obtain ⟨r,_,rfl⟩:=List.mem_map.mp hk
      exact ⟨r.receiverId,rfl⟩) pre (by
      intro key hk
      obtain ⟨account,rfl⟩:=hk
      exact (schedStep_account_read hw hsched account).symm)
  obtain ⟨_,_,_,_,_,_,_,hup⟩:=schedStep_complete hsched
  have hfinal:=SizedAccountRun.upsert_actual hreplay hwell keyBwState so.state (by
    intro q hq
    rw [hkeys] at hq
    obtain ⟨r,_,rfl⟩:=List.mem_map.mp hq
    simp [keyBwState,accountKeyPath,nibbles]) hup hwrite.forget
  exact ⟨writes,oldPost,mid,so,hsched,hkeys,hreplay,hreplay.forget.skeleton,
    SizedAccountRun.wf hreplay hwell,hreplay.value_lengths,by simpa only [hout] using hfinal⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
