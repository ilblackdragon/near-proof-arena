import ZkFormal.NearV3.Candidates.ProcessRepairBalance
import ZkFormal.NearV3.Candidates.ProcPriorRoutedVParent
namespace ZkFormal.NearV3.Candidates.ProcessRepairVParent
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
theorem balance {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VPARENT)
    {vs:List NodeS3} {es:List ValE}
    (hN:ZkFormal.Near.TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 vs))
    (hV:ZkFormal.Near.TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es)) :
    Link3.VParentBal vs es := by
  intro msg
  have ht:0<(ProcessRepairBalance.reference AP).tables.length := by change 0<ProcPriorComparatorRoutedFamily.tables.length;decide +kernel
  have hc (dir:Bool):busCount (ProcessRepairBalance.reference AP).toAir tr pub B_VPARENT dir msg=
      tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_VPARENT dir msg := by
    rw [busCount_single ht (fun t ht hn i hi hb=>(ProcPriorRoutedVParent.other_tables (AP:=ProcessRepairBalance.reference AP) rfl t ht hn i hi hb).elim)]
    rfl
  have hp (dir:Bool):pubCount (ProcessRepairBalance.reference AP) pub B_VPARENT dir msg=0 :=
    pubCount_zero (fun seg hseg hb=>absurd hb (hpub seg hseg)) msg
  have hh:=ProcessRepairBalance.balance v B_VPARENT msg
  rw [hc true,hc false,hp true,hp false,Nat.add_zero,Nat.add_zero,ProcPriorRoutedVParent.send_count,ProcPriorRoutedVParent.recv_count] at hh
  rw [(hN _ _).1,(hV _ _).2] at hh
  exact hh
end ZkFormal.NearV3.Candidates.ProcessRepairVParent
