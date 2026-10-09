import ZkFormal.NearV3.Candidates.ProcessRepairBalance
import ZkFormal.NearV3.Candidates.ProcPriorRoutedParent
namespace ZkFormal.NearV3.Candidates.ProcessRepairParent
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Near
open ZkFormal.NearV3.Sched
theorem balance {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_PARENT)
    {vs:List NodeS3} {hs:List HeadE}
    (hN:ZkFormal.Near.TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    (hHead:ZkFormal.Near.TableTraffic HeadV3.interactions tr 1 pub (headTraffic hs)) :
    Link3.ParentBal vs hs := by
  intro msg
  have hp (dir:Bool):pubCount (ProcessRepairBalance.reference AP) pub B_PARENT dir msg=0 :=
    pubCount_zero (fun seg hseg hb=>absurd hb (hpub seg hseg)) msg
  have hh:=ProcessRepairBalance.balance v B_PARENT msg
  rw [ProcPriorRoutedParent.global_count (AP:=ProcessRepairBalance.reference AP) rfl true,ProcPriorRoutedParent.global_count (AP:=ProcessRepairBalance.reference AP) rfl false,hp true,hp false,Nat.add_zero,Nat.add_zero] at hh
  rw [(hN _ _).1,(hHead _ _).1,(hN _ _).2,(hHead _ _).2] at hh
  have he:headRecvs hs B_PARENT=[] := by simp [headRecvs,B_PARENT,B_DIGEST,B_ROOT,B_EDGE]
  change _+_= _+(headRecvs hs B_PARENT |>.map ZkFormal.Near.Msg.toFp).count msg at hh
  rw [he,List.map_nil,List.count_nil,Nat.add_zero] at hh
  change ((nodeSends3 vs B_PARENT++headSends hs B_PARENT).map ZkFormal.Near.Msg.toFp).count msg=_
  rw [List.map_append,List.count_append]
  exact hh
end ZkFormal.NearV3.Candidates.ProcessRepairParent
