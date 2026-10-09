import ZkFormal.NearV3.Candidates.SortEmpty
import ZkFormal.NearV3.Candidates.ProcPriorCodecActualFamily
namespace ZkFormal.NearV3.Candidates.SortEmpty
open ZkFormal.Air ZkFormal.Near ZkFormal.Size
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem current_rest_sort : HorizontalAccounts.rest[10]?=some {Sort.table with maxLog:=18} := by rfl

theorem current_selected_sort : ProcPriorCodecActualFamily.tables[11]?=
    some (InteractionTriples.table {Sort.table with maxLog:=18}) := by rfl

theorem unchanged_shape : shapeOf 3 table=shapeOf 3 {Sort.table with maxLog:=18} := by decide +kernel

theorem unchanged_interactions : table.interactions=Sort.interactions := rfl

theorem table_wf : table.wf ⟨[table],77,202⟩ 8=true := by decide +kernel
end ZkFormal.NearV3.Candidates.SortEmpty
