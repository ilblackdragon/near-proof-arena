import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemBounds
import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemOrder
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountMemoryBalance
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof Render
open Rcpt.Candidates.NodePostUpdate

def locatedMemSends (pub : List Fp) (tr : Trace Fp) (lists : List (List Input)) : List ZkFormal.Near.Msg :=
  (receiptLocations 0 (entityPlans lists)).flatMap (fun x=>
    rSends pub [] 0 x.2.receiptIndex 0 (rcptOf tr 0 (inputShape x.1 x.2.input)) B_MEM)
def locatedMemRecvs (tr : Trace Fp) (lists : List (List Input)) : List ZkFormal.Near.Msg :=
  (receiptLocations 0 (entityPlans lists)).flatMap (fun x=>
    rRecvs x.2.receiptIndex (rcptOf tr 0 (inputShape x.1 x.2.input)) B_MEM)

/-- Aggregate the actual extracted memory fields over all physical receipt
blocks. Account IDs are original-prestate slots; no separate index or timestamp
range hypotheses are imposed on the rendered receipts. -/
theorem native_receipt_mem_aggregate (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
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
    (he:∀account,original.find (accountKeyPath account)=st.trie.find (accountKeyPath account)) :
    let accountId:=fun p:ReceiptPlan=>accountSlot original
      ((lists.flatten.map Input.receipt).map (fun r=>accountKeyPath r.receiverId)) p.receiptIndex
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId (depositConstants (depositPlanAccount steps)
        (depositAgeConstants (depositPlanPrevious lists) constants))) pub digests
      (completeReceiptAux ctx k lists accountId accessId
        (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback)) headerFallback) 0
    locatedMemSends pub tr lists=nativeLedgerMemWrites original (lists.flatten.map Input.receipt) steps ∧
    locatedMemRecvs tr lists=nativeLedgerMemReads original (lists.flatten.map Input.receipt) steps := by
  let keys:=(lists.flatten.map Input.receipt).map (fun r=>accountKeyPath r.receiverId)
  let accountId:=fun p:ReceiptPlan=>accountSlot original keys p.receiptIndex
  let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
    (completeReceiptConstants ctx k accountId (depositConstants (depositPlanAccount steps)
      (depositAgeConstants (depositPlanPrevious lists) constants))) pub digests
    (completeReceiptAux ctx k lists accountId accessId
      (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback)) headerFallback) 0
  change locatedMemSends pub tr lists=_ ∧ locatedMemRecvs tr lists=_
  have hpoint (x : Nat×ReceiptPlan) (hx:x∈receiptLocations 0 (entityPlans lists)) :
      rSends pub [] 0 x.2.receiptIndex 0 (rcptOf tr 0 (inputShape x.1 x.2.input)) B_MEM=
        ledgerMemoryLanes original steps (accountId x.2,x.2.receiptIndex+1) ∧
      rRecvs x.2.receiptIndex (rcptOf tr 0 (inputShape x.1 x.2.input)) B_MEM=
        ledgerMemoryLanes original steps (accountId x.2,closingKeyVersion (keys.getD x.2.receiptIndex []) 0 (keys.take x.2.receiptIndex)) := by
    obtain ⟨pre,post,hb,hoff⟩:=native_locations_block lists x.1 x.2 hx
    have hm:PlannedRow.receipt x.2 ⟨sPL,0,4⟩∈plannedRows lists:=by
      rw [hb]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
        (List.mem_of_getElem? (receipt_first_position x.2)))))
    have hbnd:=native_receipt_mem_bounds ctx lists original replay as ha hn hrun hgas x.2 _ hm
    have hh:=native_receipt_mem_ledger own ctx k lists log constants pub digests
      (fun p=>accountSlot original ((lists.flatten.map Input.receipt).map (fun r=>accountKeyPath r.receiverId)) p.receiptIndex)
      accessId fallback headerFallback x.2 pre post hb original st steps hl ho hv hbnd.1 (he _) hbnd.2.1 hbnd.2.2.1 [] 0 0
    rw [←hoff] at hh
    have hi:=planned_receipt_native_index lists x.2 ⟨sPL,0,4⟩ hm
    have hp:depositPlanPrevious lists x.2=
      closingKeyVersion (((lists.flatten.map Input.receipt).map (fun r=>accountKeyPath r.receiverId)).getD x.2.receiptIndex []) 0
        (((lists.flatten.map Input.receipt).map (fun r=>accountKeyPath r.receiverId)).take x.2.receiptIndex):=by
      rw [depositPlanPrevious_key]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map,hi,Option.map_some,Option.getD_some,List.map_take]
    refine ⟨hh.1,hh.2.trans ?_⟩
    exact congrArg (fun time=>ledgerMemoryLanes original steps (accountId x.2,time)) hp
  constructor
  · unfold locatedMemSends nativeLedgerMemWrites
    simp only [List.length_map]
    exact native_locations_flatMap lists _ _ (fun x hx=>(hpoint x hx).1)
  · unfold locatedMemRecvs nativeLedgerMemReads
    simp only [List.length_map]
    exact native_locations_flatMap lists _ _ (fun x hx=>(hpoint x hx).2)
end ZkFormal.NearV3.Assembly.RcptSkeleton
