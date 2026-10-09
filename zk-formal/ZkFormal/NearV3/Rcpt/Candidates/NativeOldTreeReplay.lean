import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountReplay

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0 Assembly

/-- The actual receipt writes can be replayed on the original main prestate.
The resulting old-record tree is shape-preserving and agrees on every account
read with the actual receipt-stage output. It is not the structural final trie. -/
theorem newchunk_old_tree_replay {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : TrieShape pre) (h : applyNewChunk prims ctx pre rs=.ok out) :
    ∃before after : Acc×List Limit,∃writes,∃oldPost : PTrie,
      applyReceipts ctx 0 before rs=.ok after ∧
      AccountWriteRun before.1.trie writes after.1.trie ∧
      writes.map Prod.fst=rs.map (fun r=>accountKeyPath r.receiverId) ∧
      AccountWriteRun pre writes oldPost ∧ WriteTreePair pre oldPost ∧
      ∀account,oldPost.find (accountKeyPath account)=after.1.trie.find (accountKeyPath account) := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨⟨mid,so⟩,hsched,h⟩:=bind_ok' h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨after,ha,_⟩:=bind_ok' h
  obtain ⟨writes,hwrite,hkeys⟩:=native_account_writes ctx rs 0 _ after ha
  obtain ⟨oldPost,hreplay,hshape,hreads⟩:=AccountWriteRun.rebase_skeleton hwrite
    (fun key=>∃account,key=accountKeyPath account) (by
      intro key hk
      rw [hkeys] at hk
      obtain ⟨r,_,rfl⟩:=List.mem_map.mp hk
      exact ⟨r.receiverId,rfl⟩) pre (by
      intro key hk
      obtain ⟨account,rfl⟩:=hk
      exact (schedStep_account_read hw hsched account).symm)
  exact ⟨_,after,writes,oldPost,ha,hwrite,hkeys,hreplay,hshape,
    fun account=>hreads _ ⟨account,rfl⟩⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
