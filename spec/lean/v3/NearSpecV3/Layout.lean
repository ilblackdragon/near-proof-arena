import NearSpecV3.Wire

/-!
# Shard layout (V2 / V3) and account routing

`ShardLayout` borsh (`core/primitives/src/shard_layout/mod.rs:61-69`, explicit
discriminants V0 = 0 … V3 = 3):
* V2 (`shard_layout/v2.rs:52-87`): `boundary_accounts: Vec<AccountId>, shard_ids: Vec<u64>,
  id_to_index_map: BTreeMap<u64,u64>, index_to_id_map: BTreeMap<u64,u64>,
  shards_split_map: Option<BTreeMap<u64,Vec<u64>>>, shards_parent_map: Option<BTreeMap<u64,u64>>,
  version: u32`;
* V3 (`shard_layout/v3.rs:91-120`): `boundary_accounts, shard_ids, id_to_index_map,
  shards_split_map: BTreeMap<u64,Vec<u64>>, last_split: u64, shards_ancestor_map: BTreeMap<u64,Vec<u64>>`.

`account_id_to_shard_id` (V2/V3, `v2.rs:265-268`, `v3.rs:284-287`):
`shard_ids[boundary_accounts.partition_point(|b| b <= account)]`, byte-lexicographic.
`get_shard_index` uses `id_to_index_map`.

The layout bytes are a trusted claim fact (spec/claim-v3.md T6); only V2 and V3
are in D0 (`c.layout`).
-/

namespace NearSpecV3

open NearSpec

structure Layout where
  boundaries : List Bytes
  shardIds : List Nat
  idToIndex : List (Nat × Nat)
  /-- V3 only: parent shard → the shards it split into. Empty for V2 (which carries no split map).
  This is the split's own record in the layout bytes; the validator reads it to decide whether a
  block crosses a layout boundary and which child shard a resharding transition produces. -/
  splitMap : List (Nat × List Nat) := []
  /-- V3 only: the most recent split's parent shard id. -/
  lastSplit : Option Nat := none
  /-- V3 only: child shard → its ancestor shards. -/
  ancestorMap : List (Nat × List Nat) := []
  deriving Repr

def pPairU64 : P (Nat × Nat) := fun bs => do
  let (a, bs) ← pU64 "map key" bs
  let (b, bs) ← pU64 "map value" bs
  pure ((a, b), bs)

def pKeyVecU64 : P (Nat × List Nat) := fun bs => do
  let (k, bs) ← pU64 "map key" bs
  let (vs, bs) ← pVec "map value" (pU64 "shard") bs
  pure ((k, vs), bs)

def decodeLayout (b : Bytes) : Except String Layout := do
  let (tag, bs) ← pU8 "ShardLayout tag" b
  match tag with
  | 2 => do
    let (bd, bs) ← pVec "boundary_accounts" (pAccountId "boundary") bs
    let (ids, bs) ← pVec "shard_ids" (pU64 "shard id") bs
    let (i2x, bs) ← pVec "id_to_index_map" pPairU64 bs
    let (_, bs) ← pVec "index_to_id_map" pPairU64 bs
    let (_, bs) ← pOption "shards_split_map" (pVec "split map" pKeyVecU64) bs
    let (_, bs) ← pOption "shards_parent_map" (pVec "parent map" pPairU64) bs
    let (_, bs) ← pU32 "version" bs
    if !bs.isEmpty then throw "decode: trailing bytes in ShardLayout"
    -- V2 has no V3 split map: its split information lives in the optional maps just skipped, whose
    -- shape differs (parent map is shard -> shard). V2 resharding is not modelled; the fields stay
    -- empty so a V2 layout can never claim a V3 split.
    pure { boundaries := bd, shardIds := ids, idToIndex := i2x }
  | 3 => do
    let (bd, bs) ← pVec "boundary_accounts" (pAccountId "boundary") bs
    let (ids, bs) ← pVec "shard_ids" (pU64 "shard id") bs
    let (i2x, bs) ← pVec "id_to_index_map" pPairU64 bs
    let (splitMap, bs) ← pVec "shards_split_map" pKeyVecU64 bs
    let (lastSplit, bs) ← pU64 "last_split" bs
    let (ancestorMap, bs) ← pVec "shards_ancestor_map" pKeyVecU64 bs
    if !bs.isEmpty then throw "decode: trailing bytes in ShardLayout"
    pure { boundaries := bd, shardIds := ids, idToIndex := i2x, splitMap, lastSplit := some lastSplit, ancestorMap }
  | _ => throw "out of domain (c.layout): shard layout is not V2/V3"

/-- Byte-lexicographic `a ≤ b` (Rust `str` ordering). -/
def lexLe : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLe as bs)

/-- `partition_point(|b| b <= account)` on a sorted boundary list. -/
def partitionPoint (acct : Bytes) : List Bytes → Nat
  | [] => 0
  | b :: bs => if lexLe b acct then 1 + partitionPoint acct bs else 0

def Layout.shardOf (l : Layout) (acct : Bytes) : Nat :=
  l.shardIds.getD (partitionPoint acct l.boundaries) 0

def Layout.index (l : Layout) (s : Nat) : Option Nat :=
  (l.idToIndex.find? (·.1 == s)).map (·.2)

def Layout.numShards (l : Layout) : Nat := l.shardIds.length

/-! ## V3 layout relations (`core/primitives/src/shard_layout/v3.rs:299-354`) -/

/-- The children of the layout's most recent split (`last_split_children`). -/
def Layout.lastSplitChildren (l : Layout) : List Nat :=
  match l.lastSplit with
  | some p => ((l.splitMap.find? (·.1 == p)).map (·.2)).getD []
  | none => []

/-- `ShardLayoutV3::get_children_shards_ids`: the split's children for the split parent, the shard
itself for any other shard of the layout, `none` otherwise. -/
def Layout.childrenV3 (l : Layout) (s : Nat) : Option (List Nat) :=
  if l.lastSplit == some s then some l.lastSplitChildren
  else if l.shardIds.contains s && !l.lastSplitChildren.contains s then some [s]
  else none

/-- `ShardLayoutV3::try_get_parent_shard_id`: the split parent for a child of the most recent split,
the shard itself otherwise; `none` if the shard is not in the layout. -/
def Layout.parentV3 (l : Layout) (s : Nat) : Option Nat :=
  if !l.shardIds.contains s then none
  else if l.lastSplitChildren.contains s then l.lastSplit
  else some s

end NearSpecV3
