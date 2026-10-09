import ZkFormal.NearV3.Candidates.QueueKeyRepairTraffic
import ZkFormal.NearV3.Candidates.ProcPriorCodecCertifiedAdmission
import ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair

namespace ZkFormal.NearV3.Candidates.QueueKeyRepair
open ZkFormal.Air

/-- The honest-renderer repair is the same candidate already used by the
structurally certified family, rather than a new interaction inventory. -/
theorem existing_table : table=Qv.Candidates.KeyTrafficRepair.table := rfl

theorem certified_slot : ProcPriorCodecActualFamily.selected[18]?=some table := by rfl

/-- Exact table identity links the repaired honest trace to the already
checked complete candidate admission bounds. This does not close global balance. -/
theorem retained_certificate :
    ProcPriorCodecActualFamily.selected[18]?=some table ∧
    ProcPriorCodecActualFamily.air.wf 16=true ∧
    ZkFormal.Size.sizeMaxDedup ProcPriorCodecActualFamily.air (ZkFormal.V2.G.pg 3)=8238324 ∧
    ZkFormal.Stark.headerOk ProcPriorCodecActualFamily.air (ZkFormal.V2.G.pg 3)
      (ProcPriorCodecActualFamily.tables.map (·.maxLog))=true :=
  ⟨certified_slot,ProcPriorCodecActualFamily.air_wf,ProcPriorCodecActualFamily.model_exact,
    ProcPriorCodecActualFamily.header_max⟩

end ZkFormal.NearV3.Candidates.QueueKeyRepair
