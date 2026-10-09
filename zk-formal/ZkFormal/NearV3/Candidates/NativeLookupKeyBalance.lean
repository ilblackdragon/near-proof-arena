import ZkFormal.NearV3.Candidates.NativeReceiptKeyTraffic
import ZkFormal.NearV3.Candidates.QueueKeyRepairTraffic
namespace ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton RcptV3 RcptV3Proof Rcpt.Candidates.NodePostUpdate
open Qv Qv.Candidates Qv.Candidates.CombinedWalkGen

theorem queue_key_count (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (vs : List ValueGen.Record) (log : Nat) (pub : List Fp)
    (hfit:((plan pre v pres resolve).flatMap Walk.rows).length≤2^log) (msg : List Fp) :
    tableBusCount QueueKeyRepair.interactions (mixedTrace (plan pre v pres resolve) vs log) 0 pub B_KEYNIB true msg=
      (((queueLookupQueries pre v pres resolve).flatMap
        (fun q=>RcptE.keyMsgs q.wid (q.key++[SYM_END]))).map Msg.toFp).count msg := by
  rw [tableBusCount_eq]
  change ((List.range (2^log)).flatMap _).count msg=_
  rw [QueueKeyRepair.all_keys _ vs log pub hfit]
  simp only [queueLookupQueries,List.flatMap_map]
  rfl

theorem physical_key_balance (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (accountId : ReceiptPlan→Nat)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh:2^log<Algebra.P)
    (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (vs : List ValueGen.Record) (qlog : Nat)
    (hfit:((plan pre v pres resolve).flatMap Walk.rows).length≤2^qlog)
    (pairs : List (PTrie×PTrie)) (ws : List WalkR)
    (hws:nativeQueryWalks pairs
      (allLookupQueries (lists.flatten.map Input.receipt) pre v pres resolve)=some ws)
    (previous : List WStep3) (trW : Trace Fp) (tt : Nat)
    (htW:TableTraffic WalkV3.interactions trW tt pub (walkTraffic3 (rankWalks previous ws))) :
    let trR:=RoutingQCandidate.patchTrace (booleanReceiptTrace own ctx lists log
      (completeReceiptConstants ctx k accountId constants) pub digests fallback headerFallback) 0
    let trQ:=mixedTrace (plan pre v pres resolve) vs qlog
    ∀(hL:TableLocal receiptArithmeticCandidate trR 0 pub) (bs : List ListBlock) (e : Nat),
      ListChain trR 0 0 bs e→∀msg,
      tableBusCount RcptV3.interactions trR 0 pub B_KEYNIB true msg+
        tableBusCount QueueKeyRepair.interactions trQ 0 pub B_KEYNIB true msg=
      tableBusCount WalkV3.interactions trW tt pub B_KEYNIB false msg := by
  intro trR trQ hL bs e hc msg
  have hR:=physical_keys own ctx k lists log constants pub digests accountId fallback headerFallback hw hh hL bs e hc msg
  have hQ:=queue_key_count pre v pres resolve vs qlog pub hfit msg
  have hW:=NativeQueryKey.physical_key pairs _ ws hws previous trW tt pub htW msg
  rw [hR,hQ,hW]
  simp only [allLookupQueries,List.flatMap_append,List.map_append,List.count_append]
end ZkFormal.NearV3.Candidates.NativeReceiptQueryInventory
