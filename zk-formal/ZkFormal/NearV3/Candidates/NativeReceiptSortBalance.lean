import ZkFormal.NearV3.Candidates.NativeReceiptIdBytes
import ZkFormal.NearV3.Assembly.RcptCandidateReceiptIdsTraffic

namespace ZkFormal.NearV3.Candidates.NativeReceiptSortBalance
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Assembly RcptSkeleton RcptV3 RcptV3Proof

/-- The existing native canonical receipt construction discharges the ID-view
identity. Physical receipt sends and repaired sort receives agree for the same
ordered input list, including empty receipt sources. -/
theorem physical (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log tS : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw:∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh:2^log<Algebra.P)
    (hn:lists.flatten.length≤8192) :
    let tr:=RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0
    ∀(hL:TableLocal receiptArithmeticCandidate tr 0 pub) (bs : List ListBlock) (e : Nat),
      ListChain tr 0 0 bs e→∀msg,
      tableBusCount RcptV3.interactions tr 0 pub B_RIDS true msg=
      tableBusCount SortEmpty.table.interactions
        (NativeSortIds.trace (lists.flatten.map Input.receipt)) tS pub B_RIDS false msg := by
  intro tr hL bs e hc msg
  have hf:=canonical_native_views own ctx lists log constants pub digests fallback headerFallback
    hw hh hL bs e hc
  have hi:=NativeReceiptIdBytes.located_ids own ctx lists log constants pub digests fallback headerFallback hw
  have hid:(flatR (bs.map (ListBlock.view tr 0))).map (fun r=>r.rid)=
      (lists.flatten.map Input.receipt).map (fun r=>r.receiptId.map UInt8.toNat):=by
    rw [hf]
    simpa only [List.map_map,Function.comp_def] using hi
  have hs:=(NativeSortIds.traffic (lists.flatten.map Input.receipt)
    (by simpa only [List.length_map] using hn) tS pub B_RIDS msg).2
  rw [hs,tableBusCount_eq,ReceiptCandidateProof.ListChain.rids_view_traffic hL hc true]
  rw [NativeReceiptIdBytes.view_ids _ _ pub hid]
  rfl

end ZkFormal.NearV3.Candidates.NativeReceiptSortBalance
