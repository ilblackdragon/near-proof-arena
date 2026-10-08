import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountNativeAllocation
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountLedgerFinal
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 NearSpec.TransferV1 ReexecV3D0 ZkFormal.Near Assembly Assembly.RcptSkeleton
/-- Receipt execution context for the caller's actual scheduler output and
actual native ledger, rather than a separately chosen ledger witness. -/
theorem newchunk_mem_context {ctx : ApplyCtx} {pre mid : PTrie} {so : SchedOut}
    {rs : List Receipt} {out : MainOut} (hw:TrieShape pre)
    (h:applyNewChunk prims ctx pre rs=.ok out)
    (hs:schedStep prims ctx pre=.ok (mid,so))
    {steps : List NativeDepositStep}
    (hl:nativeDepositLedger ctx ⟨mid,[],[],0,0⟩ rs=some steps) :
    ∃limits after,applyReceipts ctx 0 (⟨mid,[],[],0,0⟩,limits) rs=.ok after ∧
      after.1.trie=out.trie ∧ steps.map NativeDepositStep.receipt=rs ∧
      (∀s∈steps,s.Valid ctx) ∧
      (∀account,pre.find (accountKeyPath account)=mid.find (accountKeyPath account)) := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨⟨mid',so'⟩,hs',h⟩:=bind_ok' h
  have he:=Except.ok.inj (hs.symm.trans hs')
  cases he
  dsimp only at h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨after,ha,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  obtain ⟨_,_,h⟩:=bind_ok' h
  have hout:after.1.trie=out.trie:=by cases h;rfl
  obtain ⟨ss,hss,ho,_,hv⟩:=applyReceipts_deposit_ledger_final ctx rs 0 _ after ha
  have he:=Option.some.inj (hl.symm.trans hss)
  subst ss
  exact ⟨_,after,ha,hout,ho,hv,fun a=>(schedStep_account_read hw hs a).symm⟩
end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
