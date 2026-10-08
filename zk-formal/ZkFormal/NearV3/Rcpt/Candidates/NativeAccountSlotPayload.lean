import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountPreviousPayload
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountReadPair
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton

def ledgerSlotBytes (initial : PTrie) (steps : List NativeDepositStep) (vid t : Nat) : Option Bytes :=
  if t=0 then some ((NearSpecV3.valsOf initial).getD vid [])
  else (steps[t-1]?).map (fun s=>(ledgerWrite s).2)

theorem valueIndex_get_bytes {t : PTrie} {key : List Nat} {vid : Nat}
    (hi:valueIndex t key=some vid) : t.get key=some ((NearSpecV3.valsOf t).getD vid []) := by
  obtain ⟨raw,hr⟩:=valueIndex_defined t key vid hi
  obtain ⟨j,hj,hb⟩:=valueIndex_complete t key raw hr
  have he:vid=j:=Option.some.inj (hi.symm.trans hj)
  subst j
  rw [native_get_find,hr]
  simp [List.getD_eq_getElem?_getD,hb]

theorem ledgerSlotBytes_eq_key {original initial : PTrie} {key : List Nat} {vid : Nat}
    (hi:valueIndex original key=some vid) (he:original.find key=initial.find key)
    (steps : List NativeDepositStep) (t : Nat) :
    ledgerSlotBytes original steps vid t=ledgerVersionBytes initial key steps t := by
  by_cases ht:t=0
  · simp only [ledgerSlotBytes,ledgerVersionBytes,ht,if_true]
    rw [←valueIndex_get_bytes hi,native_get_find,native_get_find,he]
  · simp [ledgerSlotBytes,ledgerVersionBytes,ht]

/-- Receipt reads use the original forest VID even though native scheduling
may have changed compact ordinals in the intermediate trie. -/
theorem nativeDepositLedger_slot_before {ctx : ApplyCtx} {st : TransferV1.Acc} {rs : List Receipt}
    {steps : List NativeDepositStep} (h:nativeDepositLedger ctx st rs=some steps)
    (ho:steps.map NativeDepositStep.receipt=rs) (hv:∀s∈steps,s.Valid ctx)
    {j : Nat} {s : NativeDepositStep} (hj:steps[j]?=some s)
    {original : PTrie} {vid : Nat} (hi:valueIndex original (accountKeyPath s.receipt.receiverId)=some vid)
    (he:original.find (accountKeyPath s.receipt.receiverId)=st.trie.find (accountKeyPath s.receipt.receiverId)) :
    ledgerSlotBytes original steps vid (latestReceiverVersion s.receipt.receiverId 0 (rs.take j))=
      some s.account.encode := by
  rw [ledgerSlotBytes_eq_key hi he]
  exact nativeDepositLedger_version_bytes h ho hv hj

theorem nativeDepositLedger_slot_after (original : PTrie) {steps : List NativeDepositStep}
    {j : Nat} {s : NativeDepositStep} (hj:steps[j]?=some s) (vid : Nat) :
    ledgerSlotBytes original steps vid (j+1)=
      some ({s.account with amount:=s.account.amount+s.receipt.deposit}.encode) := by
  simp [ledgerSlotBytes,hj,ledgerWrite]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
