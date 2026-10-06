import ZkFormal.NearV3.Tables.Node
import ZkFormal.NearV3.IdsUps

/-!
# ZkFormal.NearV3.Tables.NodeUpb — the `nodeV3` delta for `upsV3` (to be applied by the lead)

`Tables/Node.lean` is not edited in M7b.  This module states the delta exactly
(`docs/zk-formal/UPSV3-DESIGN.md` §7) so that the budget can be kernel-checked now:

* one column `mU` (index `185`, width `186`): the use count of the row's post byte;
* two interactions (chained provider, as `EDGE`): on every active row
  `send UPB (NPOST(nid), pos, pb, len, depth, cid, 0)` and `recv UPB (…, mU)`, where `cid`
  is the window column (the child record of a window row; free elsewhere);
* no constraint (`mU` is free; the bus balance fixes it).
-/

namespace ZkFormal.NearV3.NodeV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def mU : Nat := 185
def widthU : Nat := 186

def upbMsg (uu : Expr) : List Expr := [mid K_NPOST (c nid), c pos, c pb, c len, c depth, c cid, uu]

def upbInteractions : List Interaction :=
  [ send B_UPB (c act) (upbMsg (k 0)),
    recv B_UPB (c act) (upbMsg (c mU)) ]

/-- `nodeV3` with the `UPB` delta. -/
def tableU : Table :=
  { width := widthU, constraints := constraints, interactions := interactions ++ upbInteractions,
    maxLog := maxLog }

end ZkFormal.NearV3.NodeV3
