import ZkFormal.NearV3.Candidates.ProcPriorCodecActualFamily
namespace ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
open ZkFormal.Air

/-- Share the installed scheduler comparator with prior-memory/ID requests.
Only the internal bus tag changes; payloads, gates, columns and constraints
are preserved. This avoids an extra padded interaction group, which would
exceed the prior family's fingerprint-count admission bound. -/
def route (i : Interaction) : Interaction:=
  if i.bus=69 then {i with bus:=Sched.B_SCMP} else i
def routeTable (T : Air.Table) : Air.Table:={T with interactions:=T.interactions.map route}
def selected : List Air.Table:=ProcPriorCodecActualFamily.selected.map routeTable
def raw : Air.Table:=HorizontalTables.fuse selected
def paired : Air.Table:={raw with interactions:=InteractionPairing.reorder raw.interactions}
def fused : Air.Table:=InteractionTriples.table paired
def tables : List Air.Table:=fused::(HorizontalAccounts.rest.map InteractionTriples.table)
def air : Air:=⟨tables,77,202⟩
def bytes : Nat:=ZkFormal.Size.sizeOfWeq (ZkFormal.V2.G.pg 3) (tables.map (ZkFormal.Size.shapeOf 3))

theorem route_payload (i : Interaction) :(route i).msg=i.msg := by simp [route];split <;> rfl
theorem route_mult (i : Interaction) :(route i).mult=i.mult := by simp [route];split <;> rfl
theorem route_send (i : Interaction) :(route i).send=i.send := by simp [route];split <;> rfl
theorem route_bus (i : Interaction) :(route i).bus=if i.bus=69 then Sched.B_SCMP else i.bus := by
  simp [route];split <;> rfl
theorem route_constraints (T : Air.Table) :(routeTable T).constraints=T.constraints := rfl
theorem widths :selected.map (·.width)=ProcPriorCodecActualFamily.selected.map (·.width) := by
  simp [selected,routeTable,List.map_map]
end ZkFormal.NearV3.Candidates.ProcPriorComparatorRoutedFamily
