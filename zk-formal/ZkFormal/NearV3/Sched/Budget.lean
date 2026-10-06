import ZkFormal.Near.Budget
import ZkFormal.NearV3.Sched.Tables.Cmp
import ZkFormal.NearV3.Sched.Tables.Mem
import ZkFormal.NearV3.Sched.Tables.Proc
import ZkFormal.NearV3.Sched.Tables.Scan
import ZkFormal.NearV3.Sched.Tables.Dist
import ZkFormal.NearV3.Sched.Tables.Codec

/-!
# ZkFormal.NearV3.Sched.Budget — width / interactions / `W_eq` of the scheduler tables

`W_eq = width + 8·aux + 8·quot` (L4 layout, `Near.Budget.weqTable`) at `auxGroup = g`, in the
order `schV3` (codec), `sscV3` (scan), `sprV3` (process), `smmV3` (memory), `scpV3`
(comparator), `sdsV3` (distribute). Kernel-checked in `Sched/BudgetCheck.lean`.
-/

namespace ZkFormal.NearV3.Sched.Budget

open ZkFormal.Air ZkFormal.Near.Budget

def schedTables : List ZkFormal.Air.Table :=
  [Codec.table, Scan.table, Proc.table, Mem.table, Cmp.table B_SCMP, Dist.table]

def report (g : Nat) : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  schedTables.map fun T =>
    (T.width, T.interactions.length, T.auxCount g, T.degree g, weqTable g T, T.maxLog)

def weqSched (g : Nat) : Nat := (schedTables.map (weqTable g)).sum

end ZkFormal.NearV3.Sched.Budget
