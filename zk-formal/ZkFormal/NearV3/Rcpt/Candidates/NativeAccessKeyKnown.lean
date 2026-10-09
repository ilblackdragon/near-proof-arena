import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountPrestate

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0 Assembly

theorem system_access_key_known {st out : Acc} {r : Receipt}
    (h : applySystemReceipt st r=.ok out) (he : r.signerId=r.receiverId) :
    st.trie.find (keyAccessKey r.receiverId r.signerPk)≠none := by
  intro hn
  unfold applySystemReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h); (try simp only [bind,Except.bind,pure,Except.pure,he,BEq.rfl,ite_true,hn] at h); split at h)
    | simp_all only [bind,Except.bind,pure,Except.pure,he,BEq.rfl,ite_true,hn])

/-- Account writes preserve every access-key read, including repeated refunds. -/
theorem native_access_keys_input_known (ctx : ApplyCtx) :
    ∀rs i (st out : Acc×List Limit),applyReceipts ctx i st rs=.ok out→
    ∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
      st.1.trie.find (keyAccessKey r.receiverId r.signerPk)≠none
  | [],_,_,_,_=>by intro r hr;simp at hr
  | r::rs,i,(acc,ls),out,h=>by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · obtain ⟨acc',ha,h⟩:=bind_ok' h
        obtain ⟨bytes,hs⟩:=Qv.applySystemReceipt_set ha
        intro receipt hr hp he
        rcases List.mem_cons.mp hr with rfl|hr
        · exact system_access_key_known ha he
        · exact set_known_reverse hs (native_access_keys_input_known ctx rs (i+1) (acc',ls) out h receipt hr hp he)
      · rename_i hsys
        split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩:=bind_ok' h
          obtain ⟨bytes,hs⟩:=Qv.applyReceipt_set ha
          intro receipt hr hp he
          rcases List.mem_cons.mp hr with rfl|hr
          · simp [hp] at hsys
          · exact set_known_reverse hs (native_access_keys_input_known ctx rs (i+1) (acc',ls') out h receipt hr hp he)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
