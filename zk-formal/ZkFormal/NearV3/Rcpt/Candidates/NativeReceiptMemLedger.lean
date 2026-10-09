import ZkFormal.NearV3.Rcpt.Candidates.NativeReceiptMemPackets
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountMemoryLanes
namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof Render
open Rcpt.Candidates.NodePostUpdate

/-- The same native ledger step supplies both physical receipt packets. Original
prestate IDs are retained even when the receipt-stage trie has different IDs. -/
theorem native_receipt_mem_ledger (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (pre post : List PlannedRow)
    (hb:plannedRows lists=pre++plannedReceiptRows p++post)
    (original : PTrie) (st : TransferV1.Acc) (steps : List NativeDepositStep)
    (hl:nativeDepositLedger ctx st (lists.flatten.map Input.receipt)=some steps)
    (ho:steps.map NativeDepositStep.receipt=lists.flatten.map Input.receipt)
    (hv:∀s∈steps,s.Valid ctx)
    (hi:valueIndex original (accountKeyPath p.input.receipt.receiverId)=some (accountId p))
    (he:original.find (accountKeyPath p.input.receipt.receiverId)=st.trie.find (accountKeyPath p.input.receipt.receiverId))
    (hid:accountId p<Algebra.P) (ht:p.receiptIndex<Algebra.P) (xs : List RcptE) (j o : Nat) :
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId (depositConstants (depositPlanAccount steps)
        (depositAgeConstants (depositPlanPrevious lists) constants))) pub digests
      (completeReceiptAux ctx k lists accountId accessId
        (depositFinalAux (depositPlanPrevious lists) (depositPlanAccount steps) fallback)) headerFallback) 0
    let x:=rcptOf tr 0 (inputShape pre.length p.input)
    rSends pub xs j p.receiptIndex o x B_MEM=ledgerMemoryLanes original steps (accountId p,p.receiptIndex+1) ∧
    rRecvs p.receiptIndex x B_MEM=ledgerMemoryLanes original steps (accountId p,depositPlanPrevious lists p) := by
  have hm:PlannedRow.receipt p ⟨sPL,0,4⟩∈plannedRows lists:=by
    rw [hb]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (List.mem_of_getElem? (receipt_first_position p)))))
  have hp:=planned_receipt_native_index lists p ⟨sPL,0,4⟩ hm
  have hs:=hp
  rw [←ho,List.getElem?_map] at hs
  cases hj:steps[p.receiptIndex]? with
  | none=>simp [hj] at hs
  | some s=>
    simp only [hj,Option.map_some,Option.some.injEq] at hs
    have ht':depositPlanPrevious lists p<Algebra.P:=Nat.lt_of_le_of_lt (depositPlanPrevious_bound lists p) ht
    have hh:=native_receipt_mem_packets own ctx k lists log constants pub digests accountId accessId
      (depositPlanPrevious lists) (depositPlanAccount steps) fallback headerFallback p pre post hb hid ht' xs j o
    have ha:=nativeDepositLedger_mem_after hv hj original (accountId p)
    have hr:=nativeDepositLedger_mem_before hl ho hv hj (hs ▸ hi) (hs ▸ he)
    simp only [depositPlanAccount,hj] at hh
    simp only [depositPlanPrevious,←hs] at hh ⊢
    constructor
    · exact hh.1.trans ha.symm
    · exact hh.2.trans hr.symm
end ZkFormal.NearV3.Assembly.RcptSkeleton
