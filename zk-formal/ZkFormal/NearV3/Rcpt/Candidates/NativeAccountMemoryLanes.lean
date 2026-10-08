import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountSlotPayload
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountMemoryPairs
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Assembly Assembly.RcptSkeleton Render

def nativeMemoryPacket (vid time lane : Nat) (bs : Bytes) : ZkFormal.Near.Msg :=
  let raw:=bs.map UInt8.toNat
  [vid,time,lane,raw.getD lane 0,raw.getD (16+lane) 0,
    if lane<8 then raw.getD (64+lane) 0 else 0]

def ledgerMemoryLanes (original : PTrie) (steps : List NativeDepositStep) (p : Nat×Nat) : List ZkFormal.Near.Msg :=
  (List.range 16).map (fun lane=>nativeMemoryPacket p.1 p.2 lane
    ((ledgerSlotBytes original steps p.1 p.2).getD []))

/-- Actual account bytes yield the receipt MEM lane format; storage occupies
only the first eight lanes, with the remaining lanes explicitly zero. -/
theorem nativeMemoryPacket_encode (vid time lane : Nat) (a : Account)
    (hh:a.codeHash.length=32) (hl:lane<16) :
    nativeMemoryPacket vid time lane a.encode=
      [vid,time,lane,(leBytes 16 a.amount).getD lane 0,
        (leBytes 16 a.locked).getD lane 0,
        if lane<8 then (leBytes 8 a.storageUsage).getD lane 0 else 0] := by
  simp only [nativeMemoryPacket,Account.encode,List.map_append,u128,u64,leBytes,toNats]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_map,
    List.length_append,leN_length,hh]
  have h32:lane<32:=by omega
  have h64:lane<64:=by omega
  have hl32:16+lane<32:=by omega
  have hl64:16+lane<64:=by omega
  simp [hl,h32,h64,hl32,hl64,show ¬16+lane<16 by omega,
    show ¬64+lane<64 by omega,show 16+lane-16=lane by omega,
    show 64+lane-64=lane by omega]

/-- A concrete 16-lane conservation equation over the actual native ledger
payload function. Physical receipt/account traffic is connected by the lane
identities, rather than by assuming equal digest or memory payloads. -/
theorem nativeAccount_memory_lanes {pre post : PTrie} {rs : List Receipt} {as : List AcctV}
    (h:nativeAccountViews pre post rs=some as) (steps : List NativeDepositStep) :
    let keys:=rs.map (fun r=>accountKeyPath r.receiverId)
    let slot:=accountSlot pre keys
    (((List.range rs.length).map (fun r=>(slot r,r+1))++as.map (fun (a : AcctV)=>(a.k,0))).flatMap
      (ledgerMemoryLanes pre steps)).Perm
      ((((List.range rs.length).map (fun r=>(slot r,closingKeyVersion (keys.getD r []) 0 (keys.take r)))++
        as.map (fun (a : AcctV)=>(a.k,a.tlast))).flatMap (ledgerMemoryLanes pre steps))) :=
  (nativeAccount_memory_pairs h).flatMap_right _

theorem nativeDepositLedger_mem_before {ctx : ApplyCtx} {st : TransferV1.Acc} {rs : List Receipt}
    {steps : List NativeDepositStep} (h:nativeDepositLedger ctx st rs=some steps)
    (ho:steps.map NativeDepositStep.receipt=rs) (hv:∀s∈steps,s.Valid ctx)
    {j : Nat} {s : NativeDepositStep} (hj:steps[j]?=some s)
    {original : PTrie} {vid : Nat} (hi:valueIndex original (accountKeyPath s.receipt.receiverId)=some vid)
    (he:original.find (accountKeyPath s.receipt.receiverId)=st.trie.find (accountKeyPath s.receipt.receiverId)) :
    ledgerMemoryLanes original steps (vid,latestReceiverVersion s.receipt.receiverId 0 (rs.take j))=
      (List.range 16).map (fun lane=>[vid,latestReceiverVersion s.receipt.receiverId 0 (rs.take j),lane,
        (leBytes 16 s.account.amount).getD lane 0,(leBytes 16 s.account.locked).getD lane 0,
        if lane<8 then (leBytes 8 s.account.storageUsage).getD lane 0 else 0]) := by
  obtain ⟨bs,_,hd⟩:=(hv s (List.mem_of_getElem? hj)).1.raw
  have hh:=(Sound.decode_wf hd).2.2.1
  simp only [ledgerMemoryLanes,nativeDepositLedger_slot_before h ho hv hj hi he,Option.getD_some]
  apply List.map_congr_left
  intro lane hl
  exact nativeMemoryPacket_encode _ _ lane s.account hh (List.mem_range.mp hl)

theorem nativeDepositLedger_mem_after {ctx : ApplyCtx} {steps : List NativeDepositStep}
    (hv:∀s∈steps,s.Valid ctx) {j : Nat} {s : NativeDepositStep} (hj:steps[j]?=some s)
    (original : PTrie) (vid : Nat) :
    ledgerMemoryLanes original steps (vid,j+1)=
      (List.range 16).map (fun lane=>[vid,j+1,lane,
        (leBytes 16 (s.account.amount+s.receipt.deposit)).getD lane 0,
        (leBytes 16 s.account.locked).getD lane 0,
        if lane<8 then (leBytes 8 s.account.storageUsage).getD lane 0 else 0]) := by
  obtain ⟨bs,_,hd⟩:=(hv s (List.mem_of_getElem? hj)).1.raw
  have hh:=(Sound.decode_wf hd).2.2.1
  simp only [ledgerMemoryLanes,nativeDepositLedger_slot_after original hj vid,Option.getD_some]
  apply List.map_congr_left
  intro lane hl
  exact nativeMemoryPacket_encode _ _ lane {s.account with amount:=s.account.amount+s.receipt.deposit}
    hh (List.mem_range.mp hl)

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
