import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountKnown
import ZkFormal.NearV3.Assembly.MainShape

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0 Assembly

theorem schedStep_account_read {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (hw : TrieShape pre) (h : schedStep prims ctx pre=.ok (post,so)) (account : Bytes) :
    post.find (accountKeyPath account)=pre.find (accountKeyPath account) := by
  obtain ⟨_,_,_,_,_,_,_,hu⟩:=schedStep_complete h
  apply shape_find_upsert_other _ _ _ _ _ hw (by decide) _ hu
  simp [keyBwState,accountKeyPath,nibbles]

/-- Native receipt execution proves initial-main-prestate account availability;
the intervening scheduler upsert uses a disjoint key. -/
theorem newchunk_accounts_prestate {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : TrieShape pre) (h : applyNewChunk prims ctx pre rs=.ok out) :
    ∀r∈rs,pre.find (accountKeyPath r.receiverId)≠none := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨⟨mid,so⟩,hsched,h⟩:=bind_ok' h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨after,ha,_⟩:=bind_ok' h
  intro r hr
  have hh:=native_accounts_input_known ha r hr
  change mid.find (accountKeyPath r.receiverId)≠none at hh
  rw [schedStep_account_read hw hsched r.receiverId] at hh
  exact hh

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
