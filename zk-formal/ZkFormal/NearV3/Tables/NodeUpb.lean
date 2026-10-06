import ZkFormal.NearV3.Tables.Node

/-!
# ZkFormal.NearV3.Tables.NodeUpb — the `nodeV3` `UPB` delta (applied in M7c)

The delta of `docs/zk-formal/UPSV3-DESIGN.md` §7 is now part of `Tables/Node.lean` (column
`mU = 185`, width 186, `send/recv UPB` on active rows).  `tableU` is kept as a name for the
budget (`BudgetUps.lean`).
-/

namespace ZkFormal.NearV3.NodeV3

/-- `nodeV3` with the `UPB` delta (= `table`). -/
abbrev tableU : ZkFormal.Air.Table := table

end ZkFormal.NearV3.NodeV3
