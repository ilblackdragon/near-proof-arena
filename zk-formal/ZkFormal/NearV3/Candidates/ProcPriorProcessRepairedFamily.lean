import ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
import ZkFormal.NearV3.Candidates.ProcBoundaryRepair
namespace ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedFamily
open ZkFormal.Air

/-- Install the already checked process boundary repair. No other component changes. -/
def selected : List Air.Table:=ProcPriorComparatorRoutedFamily.selected.set 10 ProcBoundaryRepair.table
def raw : Air.Table:=HorizontalTables.fuse selected
def paired : Air.Table:={raw with interactions:=InteractionPairing.reorder raw.interactions}
def fused : Air.Table:=InteractionTriples.table paired
def tables : List Air.Table:=fused::(HorizontalAccounts.rest.map InteractionTriples.table)
def air : Air:=⟨tables,77,202⟩
def bytes : Nat:=ZkFormal.Size.sizeOfWeq (ZkFormal.V2.G.pg 3) (tables.map (ZkFormal.Size.shapeOf 3))

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem length : selected.length=ProcPriorComparatorRoutedFamily.selected.length := by simp [selected]
theorem process_slot : selected[10]! =ProcBoundaryRepair.table := by decide +kernel

theorem other_slot (i : Nat) (hi:i≠10) :
    selected[i]! =ProcPriorComparatorRoutedFamily.selected[i]! := by
  simp only [selected,getElem!_def,List.getElem?_set_ne (Ne.symm hi)]

theorem interactions : selected.map Air.Table.interactions=
    ProcPriorComparatorRoutedFamily.selected.map Air.Table.interactions := by decide +kernel

theorem widths : selected.map Air.Table.width=ProcPriorComparatorRoutedFamily.selected.map Air.Table.width := by decide +kernel

theorem clocks : selected.map Air.Table.maxLog=ProcPriorComparatorRoutedFamily.selected.map Air.Table.maxLog := by decide +kernel

theorem process_constraints : (selected[10]!).constraints=
    Sched.Proc.cKind++(Sched.Proc.cKey.take 13++(List.range 16).map ProcBoundaryRepair.rotation++Sched.Proc.cKey.drop 29)++
      Sched.Proc.cHdr++Sched.Proc.cEnt := by rw [process_slot];rfl

theorem process_shape : ZkFormal.Size.shapeOf 3 (selected[10]!)=
    ZkFormal.Size.shapeOf 3 (ProcPriorComparatorRoutedFamily.selected[10]!) := by decide +kernel
end ZkFormal.NearV3.Candidates.ProcPriorProcessRepairedFamily
