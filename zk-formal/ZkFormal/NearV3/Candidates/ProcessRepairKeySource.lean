import ZkFormal.NearV3.Candidates.ProcessRepairBalance
import ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyBalance
namespace ZkFormal.NearV3.Candidates.ProcessRepairKeySource
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem query_source {AP:AirP} {tr:Trace Fp} {pub msg:List Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:pubCount AP pub B_KEYNIB true msg=0)
    (hc:0<tableBusCount WalkV3.interactions tr 2 pub B_KEYNIB false msg) :
    0<tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_KEYNIB true msg ∨
    0<tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_KEYNIB true msg := by
  have h:=ProcessRepairBalance.balance view B_KEYNIB msg
  have hp:pubCount (ProcessRepairBalance.reference AP) pub B_KEYNIB true msg=0:=hpub
  rw [hp,ProcPriorRoutedKeyCounts.global_count (AP:=ProcessRepairBalance.reference AP) rfl,
    ProcPriorRoutedKeyBalance.global_recv (AP:=ProcessRepairBalance.reference AP) rfl] at h
  omega
end ZkFormal.NearV3.Candidates.ProcessRepairKeySource
