import ZkFormal.NearV3.Candidates.ProcessRepairBalance
import ZkFormal.NearV3.Candidates.ProcPriorRoutedWalkCounts
import ZkFormal.NearV3.Candidates.ProcPriorRoutedWalkView
import ZkFormal.NearV3.Render.Ups.CompactExtract.WalkLink
namespace ZkFormal.NearV3.Candidates.ProcessRepairWalkBalance
open ZkFormal.V2 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem balance {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    {b:Nat} (hb:b=B_EDGE ∨ b=B_BMAP)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠b)
    {vs:List NodeS3} {hs:List HeadE} {ws:List WalkR} {v:List UpsSeg}
    (hN:TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    (hHead:TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs))
    (hW:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws))
    (hU:TableTraffic Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub (upsTraffic v)) :
    UpsRows.WalkBal vs hs ws v b := by
  apply List.perm_iff_count.mpr
  intro msg
  have h:=ProcessRepairBalance.balance view b msg
  have hp (dir:Bool):pubCount (ProcessRepairBalance.reference AP) pub b dir msg=0:=pubCount_zero (fun seg hseg he=>absurd he (hpub seg hseg)) msg
  rw [hp true,hp false,Nat.add_zero,Nat.add_zero,
    ProcPriorRoutedWalkCounts.global_count (AP:=ProcessRepairBalance.reference AP) rfl true msg b hb,
    ProcPriorRoutedWalkCounts.global_count (AP:=ProcessRepairBalance.reference AP) rfl false msg b hb] at h
  rw [(hN b msg).1,(hN b msg).2,(hHead b msg).1,(hHead b msg).2,
    (hW b msg).1,(hW b msg).2,(hU b msg).1,(hU b msg).2] at h
  simp only [List.map_append,List.count_append]
  simp only [nodeTraffic3,headTraffic,walkTraffic3] at h
  omega
end ZkFormal.NearV3.Candidates.ProcessRepairWalkBalance
