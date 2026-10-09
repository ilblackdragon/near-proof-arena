import ZkFormal.NearV3.Rcpt.Candidates.NativeAccessKeyKnown
import ZkFormal.NearV3.Assembly.MainShape

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0 Assembly

theorem schedStep_access_key_read {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (hw : TrieShape pre) (h : schedStep prims ctx pre=.ok (post,so)) (account : Bytes) (pk : PublicKey) :
    post.find (keyAccessKey account pk)=pre.find (keyAccessKey account pk) := by
  obtain ⟨_,_,_,_,_,_,_,hu⟩:=schedStep_complete h
  apply shape_find_upsert_other _ _ _ _ _ hw (by decide) _ hu
  simp [keyBwState,keyAccessKey,nibbles]

/-- Native system refund execution proves initial-main-prestate access-key availability;
the intervening scheduler upsert uses a disjoint key. -/
theorem newchunk_access_keys_prestate {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : TrieShape pre) (h : applyNewChunk prims ctx pre rs=.ok out) :
    ∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
      pre.find (keyAccessKey r.receiverId r.signerPk)≠none := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨⟨mid,so⟩,hsched,h⟩:=bind_ok' h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨after,ha,_⟩:=bind_ok' h
  intro r hr hp he
  have hh:=native_access_keys_input_known _ _ _ _ _ ha r hr hp he
  change mid.find (keyAccessKey r.receiverId r.signerPk)≠none at hh
  rw [schedStep_access_key_read hw hsched r.receiverId r.signerPk] at hh
  exact hh

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
