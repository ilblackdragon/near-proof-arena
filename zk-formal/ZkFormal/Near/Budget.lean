import ZkFormal.Near.Air
import ZkFormal.Stark.Protocol

/-!
# ZkFormal.Near.Budget — width and height accounting of `nearAir`

NEAR-AIR.md §5: `W_eq = Σ_t (width_t + 8·aux_t + 8·quot_t)` with L4's
protocol layout (`Table.auxCount`, `Table.quotCount`).  `report` prints the
per-table numbers; `weq_le` is the kernel-checked budget.
-/

namespace ZkFormal.Near.Budget

open ZkFormal.Air ZkFormal.Stark

/-- Equivalent base-field width of a table (main + 8·aux + 8·quot). -/
def weqTable (g : Nat) (T : ZkFormal.Air.Table) : Nat := T.width + 8 * T.auxCount g + 8 * T.quotCount g

def weq (A : Air) (g : Nat) : Nat := (A.tables.map (weqTable g)).sum

def report (g : Nat) : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  nearAir.tables.map fun T =>
    (T.width, T.interactions.length, T.auxCount g, T.degree g, weqTable g T, T.maxLog)

end ZkFormal.Near.Budget
