import ZkFormal.NearV3.Candidates.NativeAccessKeyPhysical
namespace ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly Assembly.RcptSkeleton RcptV3 RcptV3Proof
/-- Whole physical receipt/provider access-counter conservation. All selected
provider coverage, repeated uses and absent-key silence are derived. -/
theorem physical_balance (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat)
    (previous : ReceiptPlan→Nat) (accounts : ReceiptPlan→Account)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (pre : PTrie) (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh:2^log<Algebra.P)
    (trK : Trace Fp) (tk : Nat)
    (hK:TableTraffic AkeyV3.interactions trK tk pub
      (akeyTraffic (NativeAccessKeyProviders.providers pre (lists.flatten.map Input.receipt)))) :
    let rs:=lists.flatten.map Input.receipt
    let tr:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log constants pub digests
      (completeReceiptAux ctx k lists accountId (NativeReceiptAccessIds.accessId pre)
        (depositFinalAux previous accounts (rankAux pre rs fallback))) headerFallback) 0
    ∀(hL:TableLocal receiptArithmeticCandidate tr 0 pub) (bs : List ListBlock) (e : Nat),
      ListChain tr 0 0 bs e→∀msg,
      tableBusCount AkeyV3.interactions trK tk pub B_AKC true msg+
        tableBusCount RcptV3.interactions tr 0 pub B_AKC true msg=
      tableBusCount RcptV3.interactions tr 0 pub B_AKC false msg+
        tableBusCount AkeyV3.interactions trK tk pub B_AKC false msg := by
  intro rs tr hL bs e hc msg
  have hs:=physical_messages own ctx k lists log constants pub digests accountId previous accounts
    fallback headerFallback pre hw hh hL bs e hc true
  have hr:=physical_messages own ctx k lists log constants pub digests accountId previous accounts
    fallback headerFallback pre hw hh hL bs e hc false
  have hp:=((counter_balance pre rs).map Msg.toFp).count_eq msg
  simp only [List.map_append,List.count_append] at hp
  rw [(hK B_AKC msg).1,(hK B_AKC msg).2,tableBusCount_eq,tableBusCount_eq,hs,hr]
  exact hp
end ZkFormal.NearV3.Candidates.NativeAccessKeyRanks
