import ZkFormal.NearV3.Candidates.ProcessRepairInterface
import ZkFormal.NearV3.Candidates.ProcPriorRoutedNodeView
import ZkFormal.NearV3.Candidates.ProcPriorComparatorRouting
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountPrefix
namespace ZkFormal.NearV3.Candidates.ProcessRepairTrieViews
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
set_option maxRecDepth 32768

theorem node_local {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr) :
    TableLocal NodeV3.table (ProcPriorRoutedNodeView.node tr) 0 pub := by
  have h:=v.component 4 (by decide +kernel) (by decide)
  change TableLocal (ProcPriorComparatorRoutedFamily.routeTable Rcpt.Candidates.SizeCount.nodeTable)
    (ProcPriorRoutedNodeView.node tr) 0 pub at h
  exact Rcpt.Candidates.SizeCount.node_local_base ((ProcPriorComparatorRouting.local_iff _ _ _ _).mp h)

theorem value_local {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr) :
    TableLocal ValV3.table (ProcPriorRoutedRawBytes.value tr) 0 pub := by
  have h:=v.component 5 (by decide +kernel) (by decide)
  change TableLocal (ProcPriorComparatorRoutedFamily.routeTable Rcpt.Candidates.EmptyValueFusion.valueTable)
    (ProcPriorRoutedRawBytes.value tr) 0 pub at h
  have hb:TableLocal (ProcPriorValueLength.table 73) (ProcPriorRoutedRawBytes.value tr) 0 pub := by
    have hx:=(ProcPriorComparatorRouting.local_iff _ _ _ _).mp h
    refine ⟨hx.log_ge,hx.log_le,hx.constr,?_⟩
    intro r hr i hi e he
    exact hx.bits r hr i (List.mem_append_left _ hi) e he
  exact Rcpt.Candidates.SizeCount.val_local_base (ProcPriorValueLength.to_base _ _ _ _ hb)

/-- The same physical view provides both lists, preserving the offsets and
traffic APIs consumed by existing forest/value linking arguments. -/
theorem views {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (v:ProcessRepairInterface.View AP pub tr) :
    ∃ns:List NodeS3,∃vs:List ValE,NodeWf3 ns ∧ ValWf vs ∧
      TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 ns) ∧
      TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic vs) := by
  obtain ⟨ns,hn,hnt⟩:=node3_view _ pub 0 (node_local v)
  obtain ⟨vs,hv,hvt⟩:=val_view _ pub 0 (value_local v)
  exact ⟨ns,vs,hn,hv,hnt,hvt⟩

theorem repaired_views {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (h:HoldsP AP pub tr) (ht:AP.tables=ProcPriorProcessRepairedFamily.tables) :
    ∃ns:List NodeS3,∃vs:List ValE,NodeWf3 ns ∧ ValWf vs ∧
      TableTraffic NodeV3.interactions (ProcPriorRoutedNodeView.node tr) 0 pub (nodeTraffic3 ns) ∧
      TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic vs) :=
  views (ProcessRepairInterface.repaired h ht)
end ZkFormal.NearV3.Candidates.ProcessRepairTrieViews
