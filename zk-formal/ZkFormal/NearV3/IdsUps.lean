import ZkFormal.NearV3.Ids

/-!
# ZkFormal.NearV3.IdsUps — buses and SHA kind of `upsV3` (lane `v3-trie`, M7b)

`upsV3` applies the `0x0f` upsert (`docs/zk-formal/UPSV3-DESIGN.md`).  New numbers only where
nothing is agreed yet:

| # | bus | message | producers → consumers |
|---|---|---|---|
| 23 | `MEMD` | `(τ, j, i, new_i, old_i, len)` | `upsV3` node `j` (`memory_usage` byte `i`: exact new value, old value of the replaced record; its length) → `upsV3` parent node (reserved for `upsV3` in `Ids.lean`) |
| 25 | `UPB` | `(NPOST(n), pos, pb, len, depth, u)` | `nodeV3` post bytes (chained provider, use count `mU`) → `upsV3` copies (consumer: receive `u`, send `u + 1`) |
| 59 | `S0F` | `(τ, present, vid)` | `upsV3` → scheduler codec (number agreed with lane `v3-sched`) |
| 60 | `SPOST` | `(τ, pos, b)` | codec → `upsV3` (agreed, `v3-sched`) |
| 61 | `SPLEN` | `(τ, L)` | codec → `upsV3` (agreed, `v3-sched`) |

`25` is unused by every v3 lane (v3 uses `10, 11, 17 … 24`, the design reserves `12 … 16`,
`v3-sched` uses `40 … 61`).  `59 … 61` repeat `ZkFormal.NearV3.Sched.Ids` (same numbers; the
assembly identifies them).

SHA message kind `K_VUPS = 12` (registry V3-D0-DESIGN §12: 11 SCH, 12 VUPS, 13 SRC, 14 VAK):
`msgId 12 (8τ + j)`, `j = 0` the new `0x0f` value, `j = 1 … 4` the new path nodes.
-/

namespace ZkFormal.NearV3

def B_UPB : Nat := 25
def B_S0F : Nat := 59
def B_SPOST : Nat := 60
def B_SPLEN : Nat := 61

/-- SHA kind of the `upsV3` messages (`idx = 8τ + j`). -/
def K_VUPS : Nat := 12

end ZkFormal.NearV3
