import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemTraffic
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof Render
open Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
/-- Full physical receipt/account MEM conservation from the same native ledger,
including original IDs, repeated accounts, empty batches and all sixteen lanes.
Canonical ListChain correspondence and field ranges are derived internally. -/
theorem native_receipt_account_mem_balance (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (original replay : PTrie) (as : List AcctV) (st : TransferV1.Acc) (steps : List NativeDepositStep)
    (ha:nativeAccountViews original replay (lists.flatten.map Input.receipt)=some as)
    (hn:(NearSpecV3.valsOf original).length<Algebra.P)
    {t : PTrie} {out : MainOut}
    (hrun:applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas:ctx.gasLimit≤maxGasLimitD0)
    (hl:nativeDepositLedger ctx st (lists.flatten.map Input.receipt)=some steps)
    (ho:steps.map NativeDepositStep.receipt=lists.flatten.map Input.receipt)
    (hv:∀s∈steps,s.Valid ctx)
    (he:∀account,original.find (accountKeyPath account)=st.trie.find (accountKeyPath account))
    (i : Nat) (limits : List Limit) (final : TransferV1.Acc×List Limit)
    (hr:applyReceipts ctx i (st,limits) (lists.flatten.map Input.receipt)=.ok final)
    (hp:WriteTreePair original replay)
    (hpost:∀account,replay.find (accountKeyPath account)=final.1.trie.find (accountKeyPath account))
    (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh:2^log<Algebra.P)
    (trA : Trace Fp) (ta : Nat) (ia : List Interaction)
    (hA:TableTraffic ia trA ta pub (acctV3Traffic as)) :
    let accountId:=fun p:ReceiptPlan=>accountSlot original
      ((lists.flatten.map Input.receipt).map (fun r=>accountKeyPath r.receiverId)) p.receiptIndex
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId (depositConstants (depositPlanAccount steps)
        (depositAgeConstants (depositPlanPrevious lists) constants))) pub digests
      (completeReceiptAux ctx k lists accountId accessId
        (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback)) headerFallback) 0
    ∀(hL:TableLocal receiptArithmeticCandidate tr 0 pub) (bs : List ListBlock) (e : Nat),
      ListChain tr 0 0 bs e→∀msg,
      tableBusCount RcptV3.interactions tr 0 pub B_MEM true msg+
        tableBusCount ia trA ta pub B_MEM true msg=
      tableBusCount RcptV3.interactions tr 0 pub B_MEM false msg+
        tableBusCount ia trA ta pub B_MEM false msg := by
  intro accountId tr hL bs e hc msg
  have hg:=native_receipt_mem_aggregate own ctx k lists log constants pub digests accessId
    fallback headerFallback original replay as st steps ha hn hrun hgas hl ho hv he
  have hf:=canonical_native_views own ctx lists log
    (completeReceiptConstants ctx k accountId (depositConstants (depositPlanAccount steps)
      (depositAgeConstants (depositPlanPrevious lists) constants))) pub digests
    (completeReceiptAux ctx k lists accountId accessId
      (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback))
    headerFallback hw hh hL bs e hc
  have ht:=physical_located_mem tr lists pub hL bs e hc hf msg
  have hb:=native_account_memory_balance hr hl ho hv hp he hpost ha
  have hncount:=((hb.map Msg.toFp).count_eq msg)
  simp only [List.map_append,List.count_append] at hncount
  rw [ht.1,ht.2,(hA B_MEM msg).1,(hA B_MEM msg).2]
  change ((locatedMemSends pub tr lists).map Msg.toFp).count msg+
    ((acctV3Sends as B_MEM).map Msg.toFp).count msg=
    ((locatedMemRecvs tr lists).map Msg.toFp).count msg+
    ((acctRecvs as B_MEM).map Msg.toFp).count msg
  rw [hg.1,hg.2]
  exact hncount
end ZkFormal.NearV3.Assembly.RcptSkeleton
