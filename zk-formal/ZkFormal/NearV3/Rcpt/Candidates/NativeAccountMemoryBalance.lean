import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountFinalPayload
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton Render

def nativeLedgerMemWrites (pre : PTrie) (rs : List Receipt) (steps : List NativeDepositStep) : List ZkFormal.Near.Msg :=
  let keys:=rs.map (fun r=>accountKeyPath r.receiverId)
  (List.range rs.length).flatMap (fun j=>ledgerMemoryLanes pre steps (accountSlot pre keys j,j+1))

def nativeLedgerMemReads (pre : PTrie) (rs : List Receipt) (steps : List NativeDepositStep) : List ZkFormal.Near.Msg :=
  let keys:=rs.map (fun r=>accountKeyPath r.receiverId)
  (List.range rs.length).flatMap (fun j=>ledgerMemoryLanes pre steps
    (accountSlot pre keys j,closingKeyVersion (keys.getD j []) 0 (keys.take j)))

theorem nativeAccountViews_closing_mem {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    {steps : List NativeDepositStep} (hl:nativeDepositLedger ctx st.1 rs=some steps)
    (ho:steps.map NativeDepositStep.receipt=rs) (hv:∀s∈steps,s.Valid ctx)
    {original replay : PTrie} (hp:WriteTreePair original replay)
    (hpre:∀account,original.find (accountKeyPath account)=st.1.trie.find (accountKeyPath account))
    (hpost:∀account,replay.find (accountKeyPath account)=out.1.trie.find (accountKeyPath account))
    {as : List AcctV} (has:nativeAccountViews original replay rs=some as) :
    acctRecvs as B_MEM=(as.map (fun (a : AcctV)=>(a.k,a.tlast))).flatMap (ledgerMemoryLanes original steps) := by
  simp only [acctRecvs,if_true,List.flatMap_map]
  apply ZkFormal.Near.Render.flatMap_congr'
  intro a ha
  obtain ⟨after,hafter,hpay,hpostlen⟩:=nativeAccount_closing_payload h hl ho hv hp hpre hpost has a ha
  simp only [ledgerMemoryLanes,hafter,Option.getD_some]
  apply List.map_congr_left
  intro lane hmem
  exact (nativeMemoryPacket_closing a after hpay hpostlen lane (List.mem_range.mp hmem)).symm

/-- Full native MEM multiset conservation, including real account providers,
repeated receivers, all sixteen lanes, and empty receipt batches. Only the
receipt physical-renderer transport remains outside this semantic equation. -/
theorem native_account_memory_balance {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : TransferV1.Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    {steps : List NativeDepositStep} (hl:nativeDepositLedger ctx st.1 rs=some steps)
    (ho:steps.map NativeDepositStep.receipt=rs) (hv:∀s∈steps,s.Valid ctx)
    {original replay : PTrie} (hp:WriteTreePair original replay)
    (hpre:∀account,original.find (accountKeyPath account)=st.1.trie.find (accountKeyPath account))
    (hpost:∀account,replay.find (accountKeyPath account)=out.1.trie.find (accountKeyPath account))
    {as : List AcctV} (has:nativeAccountViews original replay rs=some as) :
    (nativeLedgerMemWrites original rs steps++acctV3Sends as B_MEM).Perm
      (nativeLedgerMemReads original rs steps++acctRecvs as B_MEM) := by
  rw [nativeAccountViews_initial_mem has steps,nativeAccountViews_closing_mem h hl ho hv hp hpre hpost has]
  have he:=nativeAccount_memory_lanes has steps
  simpa only [List.flatMap_append,List.flatMap_map,nativeLedgerMemWrites,nativeLedgerMemReads,
    Function.comp_def] using he

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
