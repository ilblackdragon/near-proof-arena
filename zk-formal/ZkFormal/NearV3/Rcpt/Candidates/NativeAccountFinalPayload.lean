import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountLedgerFinal
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountMemoryEndpoints
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountJobPermutation
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton Render

theorem nativeDepositLedger_final_bytes {ctx : ApplyCtx} {st : TransferV1.Acc} {rs : List Receipt}
    {steps : List NativeDepositStep} (h:nativeDepositLedger ctx st rs=some steps)
    (ho:steps.map NativeDepositStep.receipt=rs) (hv:∀s∈steps,s.Valid ctx) (receiver : Bytes) :
    ledgerVersionBytes st.trie (accountKeyPath receiver) steps (latestReceiverVersion receiver 0 rs)=
      (ledgerFinal st steps).trie.get (accountKeyPath receiver) := by
  have hlen:steps.length=rs.length:=by simpa using congrArg List.length ho
  have ht:=nativeDepositLedger_previous_version ho receiver steps.length
  rw [show rs.take steps.length=rs from List.take_of_length_le (by omega)] at ht
  have hp:=lastWriteRecord_ledger_payload st.trie (accountKeyPath receiver) steps steps.length
  simp only [List.take_length] at hp ht
  rw [←ht,hp]
  have hr:=AccountWriteRun.last_read (nativeDepositLedger_final_run h hv) (accountKeyPath receiver) 0
  simp only [native_get_find,hr]
  cases lastWriteRecord (accountKeyPath receiver) 0 (steps.map ledgerWrite) <;> rfl

theorem closingAccountView_post_length {pre post : PTrie} {keys : List (List Nat)} {key : List Nat}
    {a : AcctV} (h:closingAccountView pre post keys key=some a) : a.post.length=16 := by
  simp only [closingAccountView,bind,Option.bind] at h
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all [nativeAccountView]
  subst a
  simp [u128,leN_length]

/-- The closing MEM version carries the actual final replay bytes at the same
original occurrence ID. The ledger is the caller's actual native ledger. -/
theorem nativeAccount_closing_payload {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    {steps : List NativeDepositStep} (hl:nativeDepositLedger ctx st.1 rs=some steps)
    (ho:steps.map NativeDepositStep.receipt=rs) (hv:∀s∈steps,s.Valid ctx)
    {original replay : PTrie} (hp:WriteTreePair original replay)
    (hpre:∀account,original.find (accountKeyPath account)=st.1.trie.find (accountKeyPath account))
    (hpost:∀account,replay.find (accountKeyPath account)=out.1.trie.find (accountKeyPath account))
    {as : List AcctV} (has:nativeAccountViews original replay rs=some as) (a : AcctV) (ha:a∈as) :
    ∃after,ledgerSlotBytes original steps a.k a.tlast=some after ∧
      after.map UInt8.toNat=a.post++a.pre.drop 16 ∧ a.post.length=16 := by
  obtain ⟨key,hkey,hview⟩:=closingAccountViews_member has a ha
  obtain ⟨r,hr,hkr⟩:=List.mem_map.mp ((distinctTouched_mem key _).mp hkey)
  subst key
  have hid:=closingAccountView_id hview
  have ht:a.tlast=latestReceiverVersion r.receiverId 0 rs:=by
    rw [latestReceiverVersion_key]
    exact closingAccountView_version hview
  obtain ⟨before,after,hbefore,hafter,_,_,hpay⟩:=native_rebased_account_payload h hp hpre hpost has a ha
  have hread:replay.find (accountKeyPath r.receiverId)=some (some after):=
    indexed_value_read ((write_value_index hp _).symm.trans hid) hafter
  refine ⟨after,?_,hpay.symm,closingAccountView_post_length hview⟩
  rw [ht,ledgerSlotBytes_eq_key hid (hpre r.receiverId),nativeDepositLedger_final_bytes hl ho hv,
    nativeDepositLedger_final_state h hl,native_get_find,←hpost r.receiverId,hread]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
