import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountRebasedAllocation
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountPrestate
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 NearSpec.TransferV1 ReexecV3D0 ZkFormal.Near Assembly

theorem newchunk_account_context {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt} {out : MainOut}
    (hw:TrieShape pre) (h:applyNewChunk prims ctx pre rs=.ok out) :
    ∃before after : Acc×List Limit,applyReceipts ctx 0 before rs=.ok after ∧
      (∀account,pre.find (accountKeyPath account)=before.1.trie.find (accountKeyPath account)) ∧
      after.1.trie=out.trie := by
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
  have hout:after.1.trie=out.trie:=by cases h;rfl
  exact ⟨_,after,ha,fun account=>(schedStep_account_read hw hsched account).symm,hout⟩

/-- Whole account list on a CALLER-CHOSEN old-record replay. Its actual final
scheduler upsert discharges post keyed-read agreement with native execution;
there is no independently chosen second oldPost witness. -/
theorem newchunk_rebased_accounts {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt} {out : MainOut}
    (hw:TrieShape pre) (h:applyNewChunk prims ctx pre rs=.ok out)
    (replay : PTrie) (hp:WriteTreePair pre replay) (hwell:replay.wf=true)
    {state : Bytes} (hup:replay.upsert keyBwState state=some out.trie)
    (hn:(NearSpecV3.valsOf pre).length<Algebra.P) (hr:rs.length<Algebra.P) :
    ∃as,nativeAccountViews pre replay rs=some as ∧ as.length≤rs.length ∧
      (as=[] ∨ AcctWf as) ∧ (∀a∈as,∀b∈a.pre++a.post,b<256) ∧
      (∀m∈accountShaJobs as,∀b∈m.bytes,b<256) := by
  obtain ⟨before,after,ha,hpre,hout⟩:=newchunk_account_context hw h
  apply native_rebased_accounts ha pre replay hp hpre _ hn hr
  intro account
  rw [hout]
  exact (ZkFormal.NearV3.find_upsert_ne hwell (by decide)
    (by simp [keyBwState,accountKeyPath,nibbles]) hup).symm

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
