import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountLastWrite
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton

def ledgerWrite (s : NativeDepositStep) : List Nat×Bytes :=
  (accountKeyPath s.receipt.receiverId,({s.account with amount:=s.account.amount+s.receipt.deposit}).encode)

/-- Every incoming native ledger state is reached by exactly its preceding
writes, in receipt order. No independent prefix-state witness is chosen. -/
theorem nativeDepositLedger_prefix {ctx : ApplyCtx} {st : TransferV1.Acc} {rs : List Receipt}
    {steps : List NativeDepositStep} (h:nativeDepositLedger ctx st rs=some steps)
    (hv:∀s∈steps,s.Valid ctx) {j : Nat} {s : NativeDepositStep} (hj:steps[j]?=some s) :
    AccountWriteRun st.trie ((steps.take j).map ledgerWrite) s.before.trie := by
  induction rs generalizing st steps j with
  | nil=>simp [nativeDepositLedger] at h;subst steps;simp at hj
  | cons r rs ih=>
    simp only [nativeDepositLedger] at h
    cases ha:nativeBalanceAccount st r with
    | none=>simp [ha] at h
    | some a=>
      cases ho:nativeReceiptStep ctx st r with
      | none=>simp [ha,ho] at h
      | some out=>
        cases ht:nativeDepositLedger ctx out rs with
        | none=>simp [ha,ho,ht] at h
        | some tail=>
          simp only [ha,ho,ht,bind,Option.bind,pure,Option.some.injEq] at h
          subst steps
          cases j with
          | zero=>simp only [List.getElem?_cons_zero,Option.some.injEq] at hj;subst s;exact .nil _
          | succ j=>
            have hhead:(⟨st,r,a,out⟩:NativeDepositStep).Valid ctx:=hv _ (by simp)
            have htail:∀s∈tail,s.Valid ctx:=fun s hs=>hv s (by simp [hs])
            have hrec:=ih ht htail (by simpa using hj)
            exact .cons (ledger_account_write hhead) hrec

/-- Exact prefix lookup follows the previous concrete write, or the initial
account if this receiver has never appeared. -/
theorem nativeDepositLedger_previous_read {ctx : ApplyCtx} {st : TransferV1.Acc} {rs : List Receipt}
    {steps : List NativeDepositStep} (h:nativeDepositLedger ctx st rs=some steps)
    (hv:∀s∈steps,s.Valid ctx) {j : Nat} {s : NativeDepositStep} (hj:steps[j]?=some s) :
    s.before.trie.find (accountKeyPath s.receipt.receiverId)=
      match lastWriteRecord (accountKeyPath s.receipt.receiverId) 0 ((steps.take j).map ledgerWrite) with
      | none=>st.trie.find (accountKeyPath s.receipt.receiverId)
      | some p=>some (some p.2) :=
  AccountWriteRun.last_read (nativeDepositLedger_prefix h hv hj) _ 0

theorem nativeDepositLedger_previous_account {ctx : ApplyCtx} {st : TransferV1.Acc} {rs : List Receipt}
    {steps : List NativeDepositStep} (h:nativeDepositLedger ctx st rs=some steps)
    (hv:∀s∈steps,s.Valid ctx) {j : Nat} {s : NativeDepositStep} (hj:steps[j]?=some s) :
    (match lastWriteRecord (accountKeyPath s.receipt.receiverId) 0 ((steps.take j).map ledgerWrite) with
      | none=>st.trie.get (accountKeyPath s.receipt.receiverId)
      | some p=>some p.2).bind Account.decode=some s.account := by
  have hp:=nativeDepositLedger_previous_read h hv hj
  have hg:s.before.trie.get (accountKeyPath s.receipt.receiverId)=
      match lastWriteRecord (accountKeyPath s.receipt.receiverId) 0 ((steps.take j).map ledgerWrite) with
      | none=>st.trie.get (accountKeyPath s.receipt.receiverId)
      | some p=>some p.2 := by
    rw [native_get_find,hp]
    split
    · exact (native_get_find _ _).symm
    · rfl
  rw [←hg]
  exact nativeBalanceAccount_of_data (hv s (List.mem_of_getElem? hj)).1

theorem nativeDepositLedger_previous_version {steps : List NativeDepositStep} {rs : List Receipt}
    (ho:steps.map NativeDepositStep.receipt=rs) (receiver : Bytes) (j : Nat) :
    ((lastWriteRecord (accountKeyPath receiver) 0 ((steps.take j).map ledgerWrite)).map Prod.fst).getD 0=
      latestReceiverVersion receiver 0 (rs.take j) := by
  rw [lastWriteRecord_version,latestReceiverVersion_key,←ho]
  congr 1
  simp [List.map_map,List.map_take,ledgerWrite,Function.comp_def]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
