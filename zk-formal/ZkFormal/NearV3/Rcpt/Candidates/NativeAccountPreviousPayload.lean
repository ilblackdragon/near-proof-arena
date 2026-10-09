import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountLedgerPrefix
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountLastPosition
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton

/-- Version zero uses the initial keyed bytes; positive versions use the exact
native ledger write at that uncompressed receipt position. -/
def ledgerVersionBytes (initial : PTrie) (key : List Nat) (steps : List NativeDepositStep) (t : Nat) : Option Bytes :=
  if t=0 then initial.get key else (steps[t-1]?).map (fun s=>(ledgerWrite s).2)

theorem lastWriteRecord_ledger_payload (initial : PTrie) (key : List Nat)
    (steps : List NativeDepositStep) (j : Nat) :
    ledgerVersionBytes initial key steps
      (((lastWriteRecord key 0 ((steps.take j).map ledgerWrite)).map Prod.fst).getD 0)=
      match lastWriteRecord key 0 ((steps.take j).map ledgerWrite) with
      | none=>initial.get key
      | some p=>some p.2 := by
  cases hl:lastWriteRecord key 0 ((steps.take j).map ledgerWrite) with
  | none=>rfl
  | some p=>
    obtain ⟨n,hn,ht⟩:=lastWriteRecord_position key 0 _ hl
    have hnb:n<j:=by
      have hh:=(List.getElem?_eq_some_iff.mp hn).1
      simp only [List.length_map,List.length_take] at hh
      omega
    simp only [List.getElem?_map,List.getElem?_take,hnb,if_true] at hn
    cases hs:steps[n]? with
    | none=>simp [hs] at hn
    | some s=>
      have he:ledgerWrite s=(key,p.2):=by simpa [hs] using hn
      have hb:(ledgerWrite s).2=p.2:=congrArg Prod.snd he
      simp only [Option.map_some,Option.getD_some]
      simp [ledgerVersionBytes,ht,hs,hb]

/-- Exact native decoding at the receipt's previous version. This identifies
all amount/locked/storage bytes simultaneously, before any 16-lane projection. -/
theorem nativeDepositLedger_version_decode {ctx : ApplyCtx} {st : TransferV1.Acc} {rs : List Receipt}
    {steps : List NativeDepositStep} (h:nativeDepositLedger ctx st rs=some steps)
    (ho:steps.map NativeDepositStep.receipt=rs) (hv:∀s∈steps,s.Valid ctx)
    {j : Nat} {s : NativeDepositStep} (hj:steps[j]?=some s) :
    (ledgerVersionBytes st.trie (accountKeyPath s.receipt.receiverId) steps
      (latestReceiverVersion s.receipt.receiverId 0 (rs.take j))).bind Account.decode=some s.account := by
  rw [←nativeDepositLedger_previous_version ho s.receipt.receiverId j,lastWriteRecord_ledger_payload]
  exact nativeDepositLedger_previous_account h hv hj

theorem nativeDepositLedger_version_bytes {ctx : ApplyCtx} {st : TransferV1.Acc} {rs : List Receipt}
    {steps : List NativeDepositStep} (h:nativeDepositLedger ctx st rs=some steps)
    (ho:steps.map NativeDepositStep.receipt=rs) (hv:∀s∈steps,s.Valid ctx)
    {j : Nat} {s : NativeDepositStep} (hj:steps[j]?=some s) :
    ledgerVersionBytes st.trie (accountKeyPath s.receipt.receiverId) steps
      (latestReceiverVersion s.receipt.receiverId 0 (rs.take j))=some s.account.encode := by
  have hd:=nativeDepositLedger_version_decode h ho hv hj
  cases hb:ledgerVersionBytes st.trie (accountKeyPath s.receipt.receiverId) steps
      (latestReceiverVersion s.receipt.receiverId 0 (rs.take j)) with
  | none=>simp [hb] at hd
  | some bs=>
    have he:Account.decode bs=some s.account:=by simpa [hb] using hd
    exact congrArg some (Sound.encode_decode he).symm

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
