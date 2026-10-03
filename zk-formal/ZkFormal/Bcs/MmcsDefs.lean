import ZkFormal.Bcs.Commit

/-!
# ZkFormal.Bcs.MmcsDefs — mixed-height Merkle multi-commitment (MMCS), definitions

Byte format of lane L4 (`Stark/Bcs.lean`, `multiproof`): a tree of depth `n`
(root at level `0`, leaves at level `n`).
* leaf at level `n`: `WH(LEAF, rows)` where `rows` are the raw bytes of the
  rows of the matrices of log `n` at that index;
* node at level `k < n`: `WH(NODE, u8 k ‖ left ‖ right ‖ rows)` where `rows`
  are the raw bytes of the rows *injected* at level `k` (matrices of log `k`;
  empty if none).

An opening addresses `(ℓ, i)`: the rows stored at level `ℓ`, index `i`
(`i < 2^ℓ`), reached from the root by the bits of `i` from bit `ℓ-1` down to
bit `0`.  The value is the raw row bytes stored there.
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

/-- The log certifies that the node `node` at level `k`, followed for `t`
more levels by the low bits of `i`, stores `v`. -/
def mmcsOpen (tbl : Table) (n : Nat) : Bytes → Nat → Nat → Nat → Bytes → Prop
  | node, k, 0, _, v =>
    if k = n then WHin tbl (leafMsg v) node
    else ∃ l r, l.length = 64 ∧ r.length = 64 ∧ WHin tbl (nodeMsg k l r v) node
  | node, k, t + 1, i, v =>
    ∃ l r raw, l.length = 64 ∧ r.length = 64 ∧ WHin tbl (nodeMsg k l r raw) node ∧
      (if i / 2 ^ t % 2 = 0 then mmcsOpen tbl n l (k + 1) t i v
       else mmcsOpen tbl n r (k + 1) t i v)

/-- Extraction, mirroring `mmcsOpen` by inverting recorded wide hashes. -/
noncomputable def mmcsExt (hist : Table) (n : Nat) : Bytes → Nat → Nat → Nat → Option Bytes
  | node, k, 0, _ =>
    match invert hist node with
    | some (tg :: rest) =>
      if k = n then (if tg = tagLeaf then some rest else none)
      else if tg = tagNode then some (rest.drop 129) else none
    | _ => none
  | node, k, t + 1, i =>
    match invert hist node with
    | some (tg :: rest) =>
      if tg = tagNode then
        mmcsExt hist n (if i / 2 ^ t % 2 = 0 then (rest.drop 1).take 64 else (rest.drop 65).take 64)
          (k + 1) t i
      else none
    | _ => none

/-- The MMCS as a commitment scheme: shape = depth `n`, position = `(ℓ, i)`. -/
noncomputable def mmcs : CommitScheme where
  Shape := Nat
  Pos := Nat × Nat
  OpenIn := fun tbl root n p v => mmcsOpen tbl n root 0 p.1 p.2 v
  ext := fun hist root n p => mmcsExt hist n root 0 p.1 p.2

end ZkFormal.Bcs
