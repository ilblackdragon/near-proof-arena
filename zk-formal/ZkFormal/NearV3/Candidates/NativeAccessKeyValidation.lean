import ZkFormal.NearV3.Candidates.NativeAccessByteOwnership
import ZkFormal.NearV3.Qv.ReceiptPreserve

set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Candidates.NativeAccessKeyValidation
open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0 Assembly Rcpt.Candidates.NodePostUpdate

theorem system_valid {st out : Acc} {r : Receipt} {bytes : Bytes}
    (h : applySystemReceipt st r=.ok out) (he : r.signerId=r.receiverId)
    (hb : st.trie.find (keyAccessKey r.receiverId r.signerPk)=some (some bytes)) :
    bytes.length=9 ∧ bytes.getD 8 0=1 := by
  unfold applySystemReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h); (try simp only [bind,Except.bind,pure,Except.pure,he,BEq.rfl,ite_true,hb] at h); split at h)
    | simp_all only [bind,Except.bind,pure,Except.pure,he,hb,Bool.not_eq_true,Bool.not_eq_false,Bool.and_eq_true,beq_iff_eq])

  have hh : (!(bytes.length==9 && bytes.getD 8 0==1))=false := by assumption
  cases hx:(bytes.length==9 && bytes.getD 8 0==1) with
  | false=>rw [hx] at hh; cases hh
  | true=>simpa only [Bool.and_eq_true,beq_iff_eq] using hx

theorem receipts_valid (ctx : ApplyCtx) :
    ∀rs i (st out : Acc×List Limit),applyReceipts ctx i st rs=.ok out→
    ∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
    ∀bytes,st.1.trie.find (keyAccessKey r.receiverId r.signerPk)=some (some bytes)→
      bytes.length=9 ∧ bytes.getD 8 0=1
  | [],_,_,_,_=>by intro r hr;simp at hr
  | r::rs,i,(acc,ls),out,h=>by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · obtain ⟨acc',ha,h⟩:=bind_ok' h
        intro receipt hr hp he bytes hb
        rcases List.mem_cons.mp hr with rfl|hr
        · exact system_valid ha he hb
        · apply receipts_valid ctx rs (i+1) (acc',ls) out h receipt hr hp he bytes
          rw [Qv.applySystemReceipt_find_other ha _
            (Ne.symm (NativeAccessByteOwnership.keys_disjoint _ _ _))]
          exact hb
      · rename_i hsys
        split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩:=bind_ok' h
          intro receipt hr hp he bytes hb
          rcases List.mem_cons.mp hr with rfl|hr
          · simp [hp] at hsys
          · apply receipts_valid ctx rs (i+1) (acc',ls') out h receipt hr hp he bytes
            rw [Qv.applyReceipt_find_other ha _
              (Ne.symm (NativeAccessByteOwnership.keys_disjoint _ _ _))]
            exact hb

theorem newchunk_valid {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt}
    {out : MainOut} (hw : TrieShape pre) (h : applyNewChunk prims ctx pre rs=.ok out) :
    ∀r∈rs,r.predecessorId=AccountId.system→r.signerId=r.receiverId→
    ∀bytes,pre.find (keyAccessKey r.receiverId r.signerPk)=some (some bytes)→
      bytes.length=9 ∧ bytes.getD 8 0=1 := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨⟨mid,so⟩,hsched,h⟩:=bind_ok' h
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨after,ha,_⟩:=bind_ok' h
  intro r hr hp he bytes hb
  apply receipts_valid _ _ _ _ _ ha r hr hp he bytes
  change mid.find _=some (some bytes)
  rw [schedStep_access_key_read hw hsched,hb]

end ZkFormal.NearV3.Candidates.NativeAccessKeyValidation
