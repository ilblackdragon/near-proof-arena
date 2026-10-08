import ZkFormal.NearV3.Candidates.PriorMemoryBudget

namespace ZkFormal.NearV3.Candidates.PriorMemoryFusion
open ZkFormal.Air HorizontalProfile

/-- Provisional extra bus numbers used solely for fusion profiling. No ownership
or honest trace admission is asserted by these auxiliary-degree measurements. -/
def memory : Air.Table := ProcPriorMemoryTable.table 67 68 69

def appended : Air.Table := HorizontalTables.fuse (HorizontalReceipt.selected++[memory])
def prepended : Air.Table := HorizontalTables.fuse (memory::HorizontalReceipt.selected)

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem appended_aux_degree : appended.auxDegree 2=10 := by
  rw [auxDegree_eq]
  unfold appended
  rw [fuse_profiles,List.flatMap_append,HorizontalReceipt.profiles_equal]
  decide +kernel

theorem prepended_aux_degree : prepended.auxDegree 2=9 := by
  rw [auxDegree_eq]
  unfold prepended
  rw [fuse_profiles,List.flatMap_cons,HorizontalReceipt.profiles_equal]
  decide +kernel

end ZkFormal.NearV3.Candidates.PriorMemoryFusion
