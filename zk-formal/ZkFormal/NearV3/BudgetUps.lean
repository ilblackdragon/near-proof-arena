import ZkFormal.NearV3.Budget
import ZkFormal.NearV3.Tables.Ups
import ZkFormal.NearV3.Tables.NodeUpb

/-!
# ZkFormal.NearV3.BudgetUps — kernel-checked budget of `upsV3` and of the `nodeV3` `UPB` delta

`(width, interactions, aux, degree, W_eq, maxLog)` as in `NearV3/BudgetCheck.lean`
(`W_eq = width + 8·aux + 8·quot`, `Near.Budget.weqTable`).  `trieTablesU` is lane `v3-trie`'s
table list after M7: `nodeV3` with the delta (`NodeV3.tableU`), `headV3`, `valV3`, `walkV3`,
`uniqV3`, `upsV3`.
-/

namespace ZkFormal.NearV3.Budget

open ZkFormal.Air ZkFormal.Near.Budget

def row6 (g : Nat) (T : ZkFormal.Air.Table) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (T.width, T.interactions.length, T.auxCount g, T.degree g, weqTable g T, T.maxLog)

def trieTablesU : List ZkFormal.Air.Table :=
  [NodeV3.tableU, HeadV3.table, ValV3.table, WalkV3.table, Uniq.table, UpsV3.table]

def weqTrieU (g : Nat) : Nat := (trieTablesU.map (weqTable g)).sum

theorem ups_g1 : row6 1 UpsV3.table = (176, 15, 15, 4, 320, 22) := by decide +kernel
theorem ups_g3 : row6 3 UpsV3.table = (176, 15, 6, 8, 280, 22) := by decide +kernel

theorem nodeU_g1 : row6 1 NodeV3.tableU = (186, 20, 20, 4, 370, 22) := by decide +kernel
theorem nodeU_g3 : row6 3 NodeV3.tableU = (186, 20, 7, 8, 298, 22) := by decide +kernel

theorem weqTrieU_g1 : weqTrieU 1 = 1175 := by decide +kernel
theorem weqTrieU_g3 : weqTrieU 3 = 1063 := by decide +kernel

end ZkFormal.NearV3.Budget
