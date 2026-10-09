import ZkFormal.NearV3.Candidates.HorizontalReceipt
import ZkFormal.NearV3.Candidates.ProcPriorMemoryTable

namespace ZkFormal.NearV3.Candidates.PriorMemoryBudget
open ZkFormal.Air ZkFormal.Size

/-- Budget experiment with the prior-memory candidate as a separate table.
Bus assignments are provisional. Parser/ID tables, bus ownership and complete
trace admission remain open; this is not a new certified proof family. -/
def tables : List Air.Table := ProcPriorMemoryTable.table 0 1 2 :: HorizontalReceipt.tables

def bytes : Nat := sizeOfWeq (ZkFormal.V2.G.pg 2) (tables.map (shapeOf 2))

theorem shapes : tables.map (shapeOf 2)=
    ⟨11,3,7,3,22⟩::HorizontalAccounts.tables.map (shapeOf 2) := by
  simp only [tables,List.map_cons,ProcPriorMemoryTable.measured_shape,HorizontalReceipt.family_shapes]

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem bytes_exact : bytes=8466293 := by
  unfold bytes
  rw [shapes,HorizontalCertified.shapes]
  decide +kernel

theorem overhead : bytes-8288148=178145 := by rw [bytes_exact]

theorem exceeds_limit : bytes>8388608 := by rw [bytes_exact];decide

theorem excess : bytes-8388608=77685 := by rw [bytes_exact]

end ZkFormal.NearV3.Candidates.PriorMemoryBudget
