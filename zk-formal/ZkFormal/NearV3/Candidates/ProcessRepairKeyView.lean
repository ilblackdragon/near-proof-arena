import ZkFormal.NearV3.Candidates.ProcessRepairForeignByteTags
import ZkFormal.NearV3.Candidates.ProcPriorRoutedKeySymbols
import ZkFormal.NearV3.Candidates.ProcPriorRoutedWalkView
namespace ZkFormal.NearV3.Candidates.ProcessRepairKeyView
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
set_option maxRecDepth 32768

theorem local_key {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr) :
    TableLocal Qv.Candidates.KeyTrafficRepair.table (ProcPriorRoutedKeyView.key tr) 0 pub := by
  have h:=view.component 18 (by decide +kernel) (by decide)
  exact (ProcPriorComparatorRouting.local_iff _ _ _ _).mp h

theorem local_walk {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr) : TableLocal WalkV3.table tr 2 pub := by
  have h:=view.rest 2 (by rw [view.length];decide +kernel) (by decide)
  exact (InteractionTriples.local_iff WalkV3.table tr 2 pub).mp h

theorem walks {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr) :
    ∃ws:List WalkR,WalkWf3 ws ∧ (ws.flatMap (·.steps)).length≤2^21 ∧ TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws) :=
  walk3_view tr pub 2 (local_walk view)
end ZkFormal.NearV3.Candidates.ProcessRepairKeyView
