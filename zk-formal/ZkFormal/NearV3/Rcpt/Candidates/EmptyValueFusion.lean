import ZkFormal.NearV3.Rcpt.Candidates.EmptyValueTable
import ZkFormal.NearV3.Candidates.VerticalPriorFusion
namespace ZkFormal.NearV3.Rcpt.Candidates.EmptyValueFusion
open ZkFormal.Air ZkFormal.NearV3.Candidates

def valueTable : Air.Table := {ProcPriorValueLength.table 73 with
  interactions:=(ProcPriorValueLength.table 73).interactions++[EmptyValue.emptyInteraction]}
def selected : List Air.Table := VerticalPriorFusion.selected.set 5 valueTable
def raw : Air.Table := HorizontalTables.fuse selected
def table : Air.Table := {raw with interactions:=InteractionPairing.reorder raw.interactions}
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem value_shape : ZkFormal.Size.shapeOf 2 valueTable=⟨17,5,5,5,22⟩ := by decide +kernel
theorem value_slot : VerticalPriorFusion.selected[5]?=some (ProcPriorValueLength.table 73) := rfl
theorem width : table.width=3401 := by decide +kernel
theorem aux_degree : table.auxDegree 2=8 := by decide +kernel
theorem degree : table.degree 2=8 := by decide +kernel
theorem shape : ZkFormal.Size.shapeOf 2 table=⟨3401,115,7,115,22⟩ := by
  unfold ZkFormal.Size.shapeOf Table.quotCount
  rw [degree,HorizontalProfile.auxCount_eq,HorizontalProfile.numSide_eq,HorizontalProfile.numSide_eq,width]
  decide +kernel

def tables : List Air.Table := table::HorizontalAccounts.rest
def bytes : Nat := ZkFormal.Size.sizeOfWeq (ZkFormal.V2.G.pg 2) (tables.map (ZkFormal.Size.shapeOf 2))
theorem bytes_exact : bytes=8378132 := by
  unfold bytes
  simp only [tables,List.map_cons,shape,HorizontalAccounts.rest_shapes]
  decide +kernel
theorem below_limit : bytes<8388608 := by rw [bytes_exact];decide
end ZkFormal.NearV3.Rcpt.Candidates.EmptyValueFusion
