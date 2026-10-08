import ZkFormal.NearV3.Candidates.NativeReceiptFinalTraffic
import ZkFormal.NearV3.Candidates.NativeQueueFinalMessages
namespace ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton RcptV3 RcptV3Proof Rcpt.Candidates.NodePostUpdate
open Qv Qv.Candidates Qv.Candidates.CombinedWalkGen

theorem physical_final_balance (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh:2^log<Algebra.P)
    (pre post queryPost : PTrie) (rest : List (PTrie×PTrie)) (as : List AcctV)
    (ha:nativeAccountViews pre post (lists.flatten.map Input.receipt)=some as)
    (hn:(NearSpecV3.valsOf pre).length<Algebra.P)
    (v : MainValues) (hq:∀x∈queueInputs pre v (rest.map Prod.fst),∀r∈x.2,r.Holds x.1)
    (vs : List ValueGen.Record) (hr:∀r∈vs,r.Valid) (qlog : Nat)
    (hfit:((plan pre v (rest.map Prod.fst) (NativeQueueIds.resolve pre v (rest.map Prod.fst))).flatMap Walk.rows).length+
      ValueGen.recordsSize vs≤2^qlog)
    (ws : List WalkR)
    (hws:nativeQueryWalks ((pre,queryPost)::rest)
      (allLookupQueries (lists.flatten.map Input.receipt) pre v (rest.map Prod.fst)
        (NativeQueueIds.resolve pre v (rest.map Prod.fst)))=some ws)
    (previous : List WStep3) (trW : Trace Fp) (tt : Nat)
    (htW:TableTraffic WalkV3.interactions trW tt pub (walkTraffic3 (rankWalks previous ws))) :
    let aid:=NativeReceiptAccountIds.accountId pre (lists.flatten.map Input.receipt)
    let trR:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k aid constants) pub digests
      (completeReceiptAux ctx k lists aid (NativeReceiptAccessIds.accessId pre) fallback) headerFallback) 0
    let trQ:=mixedTrace (plan pre v (rest.map Prod.fst) (NativeQueueIds.resolve pre v (rest.map Prod.fst))) vs qlog
    ∀(hL:TableLocal receiptArithmeticCandidate trR 0 pub) (bs : List ListBlock) (e : Nat),
      ListChain trR 0 0 bs e→∀msg,
      tableBusCount WalkV3.interactions trW tt pub B_FINAL true msg=
        tableBusCount RcptV3.interactions trR 0 pub B_FINAL false msg+
        tableBusCount CombinedTable.interactions trQ 0 pub B_FINAL false msg := by
  intro aid trR trQ hL bs e hc msg
  have hR:=physical_finals own ctx k lists log constants pub digests fallback headerFallback hw hh
    pre post queryPost rest as ha hn hL bs e hc msg
  have hQ:=NativeQueueFinalMessages.physical_messages (rest.map Prod.fst) ((pre,queryPost)::rest)
    rfl hq vs hr qlog pub hfit
  have hW:=NativeQueryFinal.physical_final ((pre,queryPost)::rest) _ ws hws previous trW tt pub htW msg
  rw [hW,hR,tableBusCount_eq]
  change _= _+((List.range (2^qlog)).flatMap (fun r=>rowTraffic CombinedTable.interactions trQ 0 r pub B_FINAL false)).count msg
  rw [hQ.count_eq msg]
  simp only [allLookupQueries,List.map_append,List.count_append]
end ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
