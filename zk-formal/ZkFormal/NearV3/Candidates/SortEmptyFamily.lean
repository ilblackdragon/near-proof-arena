import ZkFormal.NearV3.Candidates.SortEmptyFamilyAdmission
namespace ZkFormal.NearV3.Candidates.SortEmptyFamily
open ZkFormal.Air ZkFormal.Size HorizontalProfile
open ProcPriorCodecActualFamily (fused)
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem shapes : tables.map (shapeOf 3)=ProcPriorCodecActualFamily.tables.map (shapeOf 3) := by
  change shapeOf 3 fused::(rest.map InteractionTriples.table).map (shapeOf 3)=
    shapeOf 3 fused::(HorizontalAccounts.rest.map InteractionTriples.table).map (shapeOf 3)
  congr 1

theorem model_exact : sizeMaxDedup air (ZkFormal.V2.G.pg 3)=8238324 := by
  rw [sizeMaxDedup_eq_model]
  change sizeOfWeq (ZkFormal.V2.G.pg 3) (tables.map (shapeOf 3))=_
  rw [shapes]
  exact ProcPriorCodecActualFamily.bytes_exact

theorem proof_bound : sizeMaxDedup air (ZkFormal.V2.G.pg 3)<8388608 := by
  rw [model_exact]
  decide
end ZkFormal.NearV3.Candidates.SortEmptyFamily
