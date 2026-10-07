import ZkFormal.NearV3.Qv.Candidates.ValueTable
import ZkFormal.Size.Model

namespace ZkFormal.NearV3.Qv.Candidates
open ZkFormal.Size

/-- Shape of the isolated parser; this is not the final queue/read table. -/
theorem value_shape_g2 : shapeOf 2 ValueTable.table = ⟨37,3,6,3,22⟩ := by decide +kernel

theorem value_constraint_count : ValueTable.constraints.length = 97 := by decide +kernel

/-- Static column/bus/degree checks only, not semantic soundness. -/
theorem value_table_wf :
    ValueTable.table.wf ⟨[ValueTable.table],64,0⟩ 4 = true := by decide +kernel

end ZkFormal.NearV3.Qv.Candidates
