import ZkFormal.Near.Budget
import ZkFormal.NearV3.Tables.Node
import ZkFormal.NearV3.Tables.Head
import ZkFormal.NearV3.Tables.Val
import ZkFormal.NearV3.Tables.Walk
import ZkFormal.NearV3.Tables.Uniq

/-!
# ZkFormal.NearV3.Budget — width / interactions / `W_eq` of the v3 trie tables

`W_eq = width + 8·aux + 8·quot` per table (L4 layout, `Near.Budget.weqTable`), at
`auxGroup = g`.  `trieTables` are lane `v3-trie`'s five tables; the numbers are
kernel-checked in `NearV3/BudgetCheck.lean`.
-/

namespace ZkFormal.NearV3.Budget

open ZkFormal.Air ZkFormal.Near.Budget

def trieTables : List ZkFormal.Air.Table :=
  [NodeV3.table, HeadV3.table, ValV3.table, WalkV3.table, Uniq.table]

/-- `(width, interactions, aux, degree, W_eq, maxLog)` per table. -/
def report (g : Nat) : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  trieTables.map fun T =>
    (T.width, T.interactions.length, T.auxCount g, T.degree g, weqTable g T, T.maxLog)

def weqTrie (g : Nat) : Nat := (trieTables.map (weqTable g)).sum

end ZkFormal.NearV3.Budget
