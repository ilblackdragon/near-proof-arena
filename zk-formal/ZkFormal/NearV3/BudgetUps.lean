import ZkFormal.NearV3.Budget
import ZkFormal.NearV3.Tables.Ups
import ZkFormal.NearV3.Tables.NodeUpb

/-!
# ZkFormal.NearV3.BudgetUps — kernel-checked budget of `upsV3` and of the `nodeV3` `UPB` delta

`(width, interactions, aux, degree, W_eq, maxLog)` as in `NearV3/BudgetCheck.lean`
(`W_eq = width + 8·aux + 8·quot`, `Near.Budget.weqTable`).  `trieTablesU` is lane `v3-trie`'s
table list after M7: `nodeV3` with the delta (`NodeV3.tableU`), `headV3`, `valV3`, `walkV3`,
`uniqV3`, `upsV3`.

M7c: `upsV3` with the pass-through mode (empty-key extensions on the `[0,15]` path), the
`UPB` child-id field and the id packing `512τ + j` (+10 columns: `dep0‥2`, `kPT`, `up`, `rc`,
`pdep`, `cN`, `rcid`, `rdc`); the `nodeV3` delta is unchanged in size (`cid` is an existing
column).  With the `VSLOT` receive (gate `valStart·tw`): `nodeV3` 21 interactions, degree 5
at `g = 1`, `W_eq` 386 / 306; lane total 1201 / 1081.  M7e (root binding): `upsV3` receives
`MIDROOT (τ, rid, mid)` into a new segment constant `rootRid` and pins the root part's source to it
(+1 column, +1 constraint, same interactions and degree): `W_eq` 331 / 291, lane total 1202 / 1082.
-/

namespace ZkFormal.NearV3.Budget

open ZkFormal.Air ZkFormal.Near.Budget

def row6 (g : Nat) (T : ZkFormal.Air.Table) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (T.width, T.interactions.length, T.auxCount g, T.degree g, weqTable g T, T.maxLog)

def trieTablesU : List ZkFormal.Air.Table :=
  [NodeV3.tableU, HeadV3.table, ValV3.table, WalkV3.table, Uniq.table, UpsV3.table]

def weqTrieU (g : Nat) : Nat := (trieTablesU.map (weqTable g)).sum

theorem ups_g1 : row6 1 UpsV3.table = (200, 15, 15, 4, 344, 22) := by decide +kernel
theorem ups_g3 : row6 3 UpsV3.table = (200, 15, 6, 8, 304, 22) := by decide +kernel

theorem nodeU_g1 : row6 1 NodeV3.tableU = (186, 21, 21, 5, 386, 22) := by decide +kernel
theorem nodeU_g3 : row6 3 NodeV3.tableU = (186, 21, 8, 8, 306, 22) := by decide +kernel

theorem weqTrieU_g1 : weqTrieU 1 = 1215 := by decide +kernel
theorem weqTrieU_g3 : weqTrieU 3 = 1095 := by decide +kernel

end ZkFormal.NearV3.Budget
