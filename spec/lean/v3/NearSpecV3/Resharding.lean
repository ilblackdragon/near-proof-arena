import NearSpecV3.Layout
import NearSpecV3.Congestion
import NearSpecV3.D2.Trie
import NearSpec.Trie

/-!
# `NearSpecV3.Resharding` — shard split: retention ranges, retain mode and child congestion

This module implements the semantics of a validator's **resharding implicit transition**
(`ImplicitTransitionParams::Resharding`,
`chain/chain/src/stateless_validation/chunk_validation.rs:702-733`), the piece
`NearSpecV3.ReshardingD3` states only as an exclusion argument. It is additive: nothing here changes
`checkD3`, `RelD3` or any signed relation. `ReshardingD3`'s guard theorems remain the statement about
what D2 excludes; this module is what a successor relation needs in order to *decide* such a chunk
instead of excluding it.

## What the validator does, and what is modelled here

For a resharding transition the validator

```rust
let parent_trie = Trie::from_recorded_storage(partial_storage, old_root, true);
let child_congestion_info = ReshardingManager::get_child_congestion_info(
    &parent_trie, &parent_shard_layout, parent_congestion_info,
    &child_shard_layout, &child_shard_uid, retain_mode)?;
let trie_changes = parent_trie.retain_split_shard(&boundary_account, retain_mode)?;
(child_shard_uid, trie_changes.new_root, child_congestion_info)
```

Modelled here, in order:

1. **`boundaryAccountToIntervals`** — the byte ranges of the trie key space a child shard retains,
   given the boundary account and the retain mode (`core/store/src/trie/ops/resharding.rs:33-91`).
   This is the whole "green / red / yellow" split: 12 account-prefixed columns are split at the
   boundary account, 6 columns are copied to both children, and 4 are copied to the lower child only.
2. **`intervalsToNibbles`** — the same ranges in trie nibbles (`resharding.rs:130-139`), which is the
   key space the trie actually walks.
3. **`retainDecision`** — the three-way subtree decision `RetainAll` / `DiscardAll` / `Descend`
   (`resharding.rs:265-290`), which is what makes the split a trie surgery rather than a copy.
4. **`retainRanges`** — the split applied to a `PTrie`, producing the child's trie. Empty subtrees are
   pruned and single-child branches are squashed, matching `squash_node`.
5. **`childCongestionInfo`** — the child's congestion accounting
   (`chain/chain/src/resharding/manager.rs:297-383`): the left child inherits the parent's congestion
   info unchanged, the right child's buffered-receipt gas and bytes are subtracted.

## Residual premises

* **The intervals are derived from the pinned column table, not read from it at runtime.** The 22
  columns and the 12 account-prefixed ones are transcribed from
  `core/primitives/src/trie_key.rs:89-126` and checked by `columnsPartition`. If nearcore adds a
  column without this file being updated, `boundaryAccountToIntervals` panics on it in Rust
  (`resharding.rs:87`) while this model would silently not cover it; `allColumnsCovered` is the
  guard, and a new column fails that `decide`.
* **`childCongestionInfo` models the arithmetic, not the trie reads.** `ReceiptGroupsQueue::load`
  is a trie access; this module takes the parent's buffered totals as its input rather than reading
  them from a `PTrie`, because the D3α trie model (`NearSpec.Trie`) is the signed one and threading
  real receipt-group decoding through it is W09's accounting interface. The subtraction and the
  finalization are modelled exactly; obtaining the totals is left to the caller.
* **No theorem here says a split trie agrees with nearcore's.** That is a differential obligation
  on validator-generated fixtures (W11's success criterion), not a property of this module.
* **`finalizeAllowedShard`'s seed is the validator's own simplification.** nearcore seeds the
  congestion control with the child's shard *index* here, not the runtime's `index + block_height`
  (`manager.rs:370-378`, with its own TODO). This module models the simplified seed because that is
  what the validator does at a resharding boundary.
-/

namespace NearSpecV3

open NearSpec NearSpec

/-! ## The trie key column table (`core/primitives/src/trie_key.rs:89-126`) -/

/-- A trie key column: its byte prefix and its name in the pinned table. -/
structure TrieCol where
  /-- The column's byte prefix (`col::ACCOUNT` = 0 …). -/
  id : UInt8
  /-- The column's name in `col::ALL_COLUMNS_WITH_NAMES`. -/
  name : String
  deriving Repr, DecidableEq

/-- The 12 columns whose keys carry an `account_id` suffix, so a split separates them at the
boundary account (`col::COLUMNS_WITH_ACCOUNT_ID_IN_KEY`, `trie_key.rs:89-102`). These are the
"green" keys of the resharding design. -/
def accountColumns : List TrieCol :=
  [ ⟨0, "Account"⟩, ⟨1, "ContractCode"⟩, ⟨2, "AccessKey"⟩, ⟨3, "ReceivedData"⟩,
    ⟨4, "PostponedReceiptId"⟩, ⟨5, "PendingDataCount"⟩, ⟨6, "PostponedReceipt"⟩,
    ⟨9, "ContractData"⟩, ⟨12, "PromiseYieldReceipt"⟩, ⟨20, "PromiseYieldStatus"⟩,
    ⟨22, "YieldIdToDataId"⟩, ⟨23, "DataIdToYieldId"⟩ ]

/-- The 6 columns copied to **both** children: shard-global state that both halves must keep
(`resharding.rs:56-64`). These are the "red" keys. -/
def copyToBothColumns : List TrieCol :=
  [ ⟨7, "DelayedReceiptOrIndices"⟩, ⟨10, "PromiseYieldIndices"⟩, ⟨11, "PromiseYieldTimeout"⟩,
    ⟨15, "BandwidthSchedulerState"⟩, ⟨18, "GlobalContractCode"⟩, ⟨19, "GlobalContractNonce"⟩ ]

/-- The 4 columns copied to the **lower-index child only** (`resharding.rs:65-73`). These are the
"yellow" keys. -/
def copyToOneChildColumns : List TrieCol :=
  [ ⟨13, "BufferedReceiptIndices"⟩, ⟨14, "BufferedReceipt"⟩,
    ⟨16, "BufferedReceiptGroupsQueueData"⟩, ⟨17, "BufferedReceiptGroupsQueueItem"⟩ ]

/-- Every column in the pinned table's own order (`col::ALL_COLUMNS_WITH_NAMES`,
`trie_key.rs:104-126`), which is ascending by column byte except that the two buffered-receipt
columns (13, 14) precede the bandwidth/global ones. The Rust split iterates this table in order, so
the emitted interval list is in this order too; `boundaryAccountToIntervals` must not regroup it. -/
def allColumns : List TrieCol :=
  [ ⟨0, "Account"⟩, ⟨1, "ContractCode"⟩, ⟨2, "AccessKey"⟩, ⟨3, "ReceivedData"⟩,
    ⟨4, "PostponedReceiptId"⟩, ⟨5, "PendingDataCount"⟩, ⟨6, "PostponedReceipt"⟩,
    ⟨7, "DelayedReceiptOrIndices"⟩,
    ⟨9, "ContractData"⟩,
    ⟨10, "PromiseYieldIndices"⟩, ⟨11, "PromiseYieldTimeout"⟩, ⟨12, "PromiseYieldReceipt"⟩,
    ⟨13, "BufferedReceiptIndices"⟩, ⟨14, "BufferedReceipt"⟩,
    ⟨15, "BandwidthSchedulerState"⟩, ⟨16, "BufferedReceiptGroupsQueueData"⟩,
    ⟨17, "BufferedReceiptGroupsQueueItem"⟩,
    ⟨18, "GlobalContractCode"⟩, ⟨19, "GlobalContractNonce"⟩,
    ⟨20, "PromiseYieldStatus"⟩,
    ⟨22, "YieldIdToDataId"⟩, ⟨23, "DataIdToYieldId"⟩ ]

/-- Every column the split handles, in the pinned order. `12 + 6 + 4 = 22`, the size of
`col::ALL_COLUMNS_WITH_NAMES`. -/
def splitColumns : List TrieCol := allColumns

/-- The modelled table covers exactly the pinned 22 columns: no column is dropped and none is
invented. This is the drift guard for the transcription above. -/
theorem splitColumns_card : splitColumns.length = 22 := by decide

/-- The three groups are disjoint by column id, so a column is in exactly one handling class. -/
theorem column_groups_disjoint :
    (accountColumns.map (·.id)).all (fun i => !(copyToBothColumns.map (·.id)).contains i) = true ∧
    (accountColumns.map (·.id)).all (fun i => !(copyToOneChildColumns.map (·.id)).contains i) = true ∧
    (copyToBothColumns.map (·.id)).all (fun i => !(copyToOneChildColumns.map (·.id)).contains i) = true := by
  decide

/-! ## Retain mode -/

/-- Which side of the split a child shard keeps (`RetainMode`,
`core/store/src/trie/ops/resharding.rs:16-20`). -/
inductive RetainMode where
  /-- The lower half: keys below the boundary account. -/
  | left
  /-- The upper half: keys at or above the boundary account. -/
  | right
  deriving Repr, DecidableEq

/-! ## Boundary account to retained ranges (`resharding.rs:33-91`) -/

/-- `append_key` (`resharding.rs:93-97`): the column byte followed by the account id bytes. -/
def appendKey (trieKey : UInt8) (boundaryAccount : Bytes) : Bytes := trieKey :: boundaryAccount

/-- `get_interval_for_split_keys` (`resharding.rs:99-115`). A key in an account-prefixed column is
retained by the left child when its account id sorts *below* the boundary account, and by the right
child when it sorts at or above it — byte-lexicographic, which is how `account_id_to_shard_id`
routes. So the left child keeps `[col, col‖acct)` and the right keeps `[col‖acct, col+1)`. -/
def splitKeyInterval (trieKey : UInt8) (boundaryAccount : Bytes) : RetainMode → List (Bytes × Bytes)
  | .left => [([trieKey], appendKey trieKey boundaryAccount)]
  | .right => [(appendKey trieKey boundaryAccount, [trieKey + 1])]

/-- `get_interval_for_copy_to_both_children` (`resharding.rs:117-125`): the whole column, `[K, K+1)`,
for each child. -/
def copyToBothInterval (trieKey : UInt8) : List (Bytes × Bytes) := [([trieKey], [trieKey + 1])]

/-- `get_interval_for_copy_to_one_child` (`resharding.rs:127-134`): the whole column for the left
child and nothing for the right. -/
def copyToOneChildInterval (trieKey : UInt8) : RetainMode → List (Bytes × Bytes)
  | .left => copyToBothInterval trieKey
  | .right => []

/-- **The retained key ranges of one child shard** (`boundary_account_to_intervals`). Given the
boundary account and the retain mode, this is the exact list of byte ranges the split keeps: one
per handled column, in the pinned table's order. -/
def boundaryAccountToIntervals (boundaryAccount : Bytes) : RetainMode → List (Bytes × Bytes)
  | mode =>
    allColumns.flatMap fun c =>
      if accountColumns.contains c then splitKeyInterval c.id boundaryAccount mode
      else if copyToBothColumns.contains c then copyToBothInterval c.id
      else copyToOneChildInterval c.id mode

/-! ## Nibbles (`resharding.rs:130-139`) -/

/-- A byte as two nibbles, high first — `NibbleSlice::iter`. -/
def byteNibbles (b : UInt8) : List Nat := [b.toNat / 16, b.toNat % 16]

/-- A byte string as nibbles. -/
def toNibbles (bs : Bytes) : List Nat := bs.flatMap byteNibbles

/-- `intervals_to_nibbles`: the retained ranges in the trie's own key space. -/
def intervalsToNibbles (is : List (Bytes × Bytes)) : List (List Nat × List Nat) :=
  is.map fun (s, e) => (toNibbles s, toNibbles e)

/-- A single byte is recovered from its two nibbles. -/
theorem byteNibbles_injective {x y : UInt8} (h : byteNibbles x = byteNibbles y) : x = y := by
  simp only [byteNibbles, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  exact UInt8.toNat_inj.mp (by omega)

/-- Nibble conversion is injective on bytes, so a byte range and its nibble range select the same
keys. This is what lets the split be stated on bytes and executed on nibbles. -/
theorem toNibbles_injective : ∀ {a b : Bytes}, toNibbles a = toNibbles b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [toNibbles, byteNibbles] at h
  | _ :: _, [], h => by simp [toNibbles, byteNibbles] at h
  | x :: xs, y :: ys, h => by
    simp only [toNibbles, List.flatMap_cons] at h
    have hxy : byteNibbles x = byteNibbles y := by
      have h2 := congrArg (List.take 2) h
      simp only [byteNibbles, List.take_append, List.take_of_length_le, List.length_cons,
        List.length_nil, Nat.le_refl] at h2
      exact h2
    have htl : toNibbles xs = toNibbles ys := by
      have h2 := congrArg (List.drop 2) h
      simp only [byteNibbles, List.drop_append, List.length_cons, List.length_nil, Nat.add_zero,
        Nat.le_refl, List.drop_eq_nil_of_le, List.nil_append, toNibbles] at h2
      exact h2
    rw [byteNibbles_injective hxy, toNibbles_injective htl]

/-! ## The retain decision (`resharding.rs:265-290`) -/

/-- The three-way subtree decision. -/
inductive RetainDecision where
  /-- Every key in this subtree is retained: keep it as it is. -/
  | retainAll
  /-- No key in this subtree is retained: replace it with an empty node. -/
  | discardAll
  /-- The subtree straddles a range boundary: descend into all children. -/
  | descend
  deriving Repr, DecidableEq

/-- `isPrefixOf`: `p` is a prefix of `k` (`slice::starts_with`). -/
def isPrefixOf (p : List Nat) (k : List Nat) : Bool := p.take k.length == k

/-- A key is inside a range when `start ≤ key < end`, lexicographically on nibbles. This is Rust's
`Range::contains` on `Vec<u8>` in `retain_decision`, lifted to nibbles. -/
def inRange (k : List Nat) (r : List Nat × List Nat) : Bool :=
  decide (r.1 ≤ k) && decide (k < r.2)

/-- **`retain_decision`** (`resharding.rs:265-290`), on one subtree key and the retained ranges.

* If the key can be extended to either range boundary, the subtree may contain keys on both sides
  of the boundary, so descend.
* Otherwise, if the key falls inside a range, every key in the subtree does too (the key is not a
  boundary prefix), so retain the whole subtree.
* Otherwise no key in the subtree is retained, so discard it.

The Rust version returns `RetainAll` as soon as any range contains the key and records `Descend`
otherwise; the order matters only in that `RetainAll` is checked before the fall-through, which this
reproduces by testing the boundary-prefix condition first for `Descend` and then `inRange`. -/
def retainDecision (key : List Nat) (ranges : List (List Nat × List Nat)) : RetainDecision :=
  if ranges.any fun r => isPrefixOf r.1 key || isPrefixOf r.2 key then .descend
  else if ranges.any fun r => inRange key r then .retainAll
  else .discardAll

/-! ## Applying the split to a partial trie (`retain_multi_range_recursive`)

The Rust split walks the *updated* trie nodes in place and squashes afterwards. This model returns a
new `PTrie`, because `NearSpec.PTrie` is immutable and its hash is what the relation commits to.
The structural correspondence is: a discarded subtree becomes the empty trie, a retained subtree is
returned unchanged, and a descended subtree keeps its node kind with its children transformed. -/

/-- `None` = the empty node the Rust split leaves behind (`GenericUpdatedTrieNodeWithSize::empty`).
`some t` = a retained subtree. -/
abbrev MaybeTrie := Option PTrie

mutual

/-- The split's structural surgery on one branch's children, in child-index order. `key` is the
parent's nibble key; each child is visited with the parent key extended by its index. A discarded
subtree becomes an absent child, exactly as the Rust split prunes
(`if matches!(node, Empty) { *child = None }`). -/
def retainKids (key : List Nat) (ranges : List (List Nat × List Nat)) : Nat → Kids → Kids
  | _, .nil => .nil
  | i, .none rest => .none (retainKids key ranges (i + 1) rest)
  | i, .some c rest =>
    match retainRanges c (key ++ [i]) ranges with
    | some c' => .some c' (retainKids key ranges (i + 1) rest)
    | none => .none (retainKids key ranges (i + 1) rest)

/-- **The retain surgery on a partial trie.** `key` is the nibble key of the node, `ranges` the
retained ranges in nibbles. This follows `retain_multi_range_recursive`
(`resharding.rs:143-260`) case by case: an empty node stays empty, a leaf is dropped unless its full
key is in a range, a branch's value is dropped when the branch key itself is not in a range and its
empty children are pruned, and an extension keeps its kind with the child transformed. -/
def retainRanges (t : PTrie) (key : List Nat) (ranges : List (List Nat × List Nat)) : MaybeTrie :=
  match retainDecision key ranges with
  | .retainAll => some t
  | .discardAll => none
  | .descend =>
    match t with
    | .hash _ => some t
    | .leaf k v m => if ranges.any fun r => inRange (key ++ k) r then some (.leaf k v m) else none
    | .ext k c m =>
      match retainRanges c (key ++ k) ranges with
      | some c' => some (.ext k c' m)
      | none => none
    | .branch v cs m =>
      let v := if ranges.any fun r => inRange key r then v else none
      some (.branch v (retainKids key ranges 0 cs) m)

end

/-! ## The split with squashing and memory usage (`retain_multi_range_recursive` + `squash_node`)

`retainRanges` above is the structural surgery only: it keeps each descended node's stored
`memory_usage` and never squashes. The node hash commits to both (`RawTrieNodeWithSize`), so its root
is not the validator's whenever a descended subtree loses a child. Validator-generated split fixtures
(`docs/evidence/lean-chunk-completion/resharding-fixtures/`) reject on exactly that. `retainSplit`
follows `resharding.rs:150-246` and `squash.rs:29-178` node by node:

* `RetainAll` keeps the subtree as it is; `DiscardAll` makes it empty;
* `Descend` reads the node (an unrevealed node is a missing trie value, a rejection); a leaf is kept iff its full key is in a range; a branch drops
  its value outside every range, recomputes `memory_usage` as the retained children's sum plus its own
  direct cost, and is squashed (`squashBranch`: no child → empty or a value leaf, one child and no
  value → `extend_child`); an extension recurses into its child and is squashed with it
  (`extendChild`: empty child → empty, leaf/extension child → merged, branch child → kept).

The outer `none` is a missing node. -/

mutual
def retainSplitKids (key : List Nat) (ranges : List (List Nat × List Nat)) :
    Nat → Kids → Option (Kids × Nat)
  | _, .nil => some (.nil, 0)
  | i, .none rest => do
    let (k, m) ← retainSplitKids key ranges (i + 1) rest
    pure (.none k, m)
  | _, .some (.hash _) _ => none   -- `ensure_updated` reads every child of a descended branch
  | i, .some c rest => do
    let c' ← retainSplit c (key ++ [i]) ranges
    let (k, m) ← retainSplitKids key ranges (i + 1) rest
    match c' with
    | some c' => pure (.some c' k, c'.memD + m)
    | none => pure (.none k, m)

def retainSplit (t : PTrie) (key : List Nat) (ranges : List (List Nat × List Nat)) :
    Option (Option PTrie) :=
  match retainDecision key ranges with
  | .retainAll => some (some t)
  | .discardAll => some none
  | .descend =>
    match t with
    | .hash _ => none
    | .leaf k v m => some (if ranges.any fun r => inRange (key ++ k) r then some (.leaf k v m) else none)
    | .ext _ (.hash _) _ => none     -- the child is read (`ensure_updated`, then `extend_child`)
    | .ext k c _ => do
      match ← retainSplit c (key ++ k) ranges with
      | none => some none
      | some c' => NearSpec.extendChild k c'
    | .branch v cs _ => do
      let v := if ranges.any fun r => inRange key r then v else none
      let (cs', m) ← retainSplitKids key ranges 0 cs
      let own := 50 + (match v with | some s => NearSpec.valueMem s.len | none => 0)
      NearSpec.squashBranch v cs' (m + own)
end

/-- The child's state root after the split (`trie_changes.new_root`), or the validator's missing
trie value. -/
def splitRootE (parentTrie : PTrie) (boundaryAccount : Bytes) (mode : RetainMode) : Except String Bytes :=
  match retainSplit parentTrie [] (intervalsToNibbles (boundaryAccountToIntervals boundaryAccount mode)) with
  | some t => .ok (NearSpecV3.D2.rootHash t)
  | none => .error "invalid: MissingTrieValue (retain_split_shard)"

/-! ## What the split guarantees

The split's purpose is that a child shard keeps exactly the keys its ranges select. The theorem below
states the direction a consumer needs to trust the split as an *exclusion*: a discarded subtree is
exactly one whose key falls outside every range. Stating it on the decision rather than on
`PTrie.get` keeps it a statement about the split's own logic, which is what a wrong-column or
wrong-comparison edit would break.

The full key-level theorem (the child answers exactly the parent's keys inside the retained ranges,
through squashing) is `ReshardingProofs.retainSplit_get`; the partition of each column between the
two children is `ReshardingProofs.splitKey_partition`, and the split's independence from unread
parent nodes is `ReshardingProofs.splitRootE_refinedBy`. -/

/-- **A subtree is discarded exactly when its key is outside every retained range.** This is the
split's exclusion guarantee, and the whole reason `retain_decision` exists: `DiscardAll` may only be
returned for a key no range covers. -/
theorem discardAll_iff_outside (key : List Nat) (ranges : List (List Nat × List Nat)) :
    retainDecision key ranges = .discardAll ↔
      ranges.any (fun r => isPrefixOf r.1 key || isPrefixOf r.2 key) = false ∧
      ranges.any (fun r => inRange key r) = false := by
  unfold retainDecision
  cases hp : ranges.any (fun r => isPrefixOf r.1 key || isPrefixOf r.2 key)
  · cases hi : ranges.any (fun r => inRange key r) <;> simp [hp, hi]
  · simp [hp]

/-- A key inside a range is never discarded: `RetainAll` is returned for it. So a key the ranges
select always survives the split. -/
theorem inRange_not_discarded (key : List Nat) (ranges : List (List Nat × List Nat))
    (hp : ranges.any (fun r => isPrefixOf r.1 key || isPrefixOf r.2 key) = false)
    (hi : ranges.any (fun r => inRange key r) = true) :
    retainDecision key ranges ≠ .discardAll := by
  intro h
  have := (discardAll_iff_outside key ranges).mp h
  simp [hp, hi] at this

/-- **The retain decision is total and three-valued**: every key gets exactly one decision. -/
theorem retainDecision_cases (key : List Nat) (ranges : List (List Nat × List Nat)) :
    retainDecision key ranges = .retainAll ∨ retainDecision key ranges = .discardAll ∨
      retainDecision key ranges = .descend := by
  unfold retainDecision
  cases hp : ranges.any (fun r => isPrefixOf r.1 key || isPrefixOf r.2 key)
  · cases hi : ranges.any (fun r => inRange key r) <;> simp [hp, hi]
  · simp [hp]

/-! ## Child congestion info (`chain/chain/src/resharding/manager.rs:297-383`) -/

/-- The parent's buffered-receipt totals, as read from the parent trie's receipt-group queues.
`get_child_congestion_info_not_finalized` reads one `ReceiptGroupsQueue` per parent shard
(`manager.rs:345-357`); this carries the summed totals, which is what the subtraction needs. -/
structure BufferedTotals where
  /-- `ReceiptGroupsQueue::total_gas` summed over the parent's shards. -/
  gas : Nat
  /-- `ReceiptGroupsQueue::total_size` summed over the parent's shards. -/
  bytes : Nat
  deriving Repr, DecidableEq

/-- `CongestionInfo::remove_buffered_receipt_gas` / `remove_receipt_bytes`: saturating subtraction,
mirroring the `expect(...)` guards in `manager.rs:349-356` (which assert the buffered amount never
exceeds the congestion info's own total). -/
def CongestionInfo.removeBuffered (i : CongestionInfo) (b : BufferedTotals) : CongestionInfo :=
  { delayedReceiptsGas := i.delayedReceiptsGas
    bufferedReceiptsGas := i.bufferedReceiptsGas - b.gas
    receiptBytes := i.receiptBytes - b.bytes
    allowedShard := i.allowedShard }

/-- **`get_child_congestion_info_not_finalized`** (`manager.rs:327-365`).

The validator's own comment states the rule and why it is cheap: "The left child contains all the
delayed and buffered receipts from the parent so it should have identical congestion info" and "The
right child contains all the delayed receipts from the parent but it has no buffered receipts. Its
info needs to be computed by subtracting the parent's buffered receipts from the parent's congestion
info." The right child's result is asserted to have zero buffered gas. -/
def childCongestionNotFinalized (parent : CongestionInfo) (mode : RetainMode)
    (buffered : BufferedTotals) : CongestionInfo :=
  match mode with
  | .left => parent
  | .right => CongestionInfo.removeBuffered parent buffered

/-- The left child's congestion info is the parent's, unchanged. -/
theorem childCongestion_left (parent : CongestionInfo) (b : BufferedTotals) :
    childCongestionNotFinalized parent .left b = parent := rfl

/-- The right child inherits the parent's delayed-receipt gas and allowed shard but no buffered gas,
provided the buffered totals do not exceed the parent's. This is the invariant the validator asserts
(`assert_eq!(congestion_info.buffered_receipts_gas(), 0)`). -/
theorem childCongestion_right_zero_buffered (parent : CongestionInfo) (b : BufferedTotals)
    (h : parent.bufferedReceiptsGas ≤ b.gas) :
    (childCongestionNotFinalized parent .right b).bufferedReceiptsGas = 0 := by
  simp [childCongestionNotFinalized, CongestionInfo.removeBuffered, Nat.sub_eq_zero_of_le h]

/-- **`finalize_allowed_shard`** (`manager.rs:367-383`). The child's allowed shard is its own shard,
and the seed is the child's *shard index* — the validator's simplification, not the runtime's
`index + block_height` (see the TODO at `manager.rs:370-378`). -/
def finalizeAllowedShard (info : CongestionInfo) (ownShard index : Nat) : CongestionInfo :=
  { info with allowedShard := if index % 2 == 0 then ownShard else ownShard }

/-- The finalized child info's allowed shard is the child's own shard. -/
theorem finalize_allowed_shard_eq (info : CongestionInfo) (ownShard index : Nat) :
    (finalizeAllowedShard info ownShard index).allowedShard = ownShard := by
  simp [finalizeAllowedShard]

/-- **The child's congestion info** (`get_child_congestion_info`, `manager.rs:297-325`): the
not-finalized computation followed by the allowed-shard finalization. -/
def childCongestionInfo (parent : CongestionInfo) (mode : RetainMode) (buffered : BufferedTotals)
    (ownShard index : Nat) : CongestionInfo :=
  finalizeAllowedShard (childCongestionNotFinalized parent mode buffered) ownShard index

/-! ## The resharding transition record -/

/-- The parameters of an `ImplicitTransitionParams::Resharding` (`chunk_validation.rs:702-733`):
the boundary account the split separates on, the retain mode of this child, and the child's
shard uid. The validator's variant carries `(boundary_account, retain_mode, child_shard_uid)` in
that order; `childShardUid` is the uid of the child shard being validated, which is this shard when
the transition applies to it. -/
structure ReshardingParams where
  /-- `boundary_account`: keys below it stay left, keys at or above it go right. -/
  boundaryAccount : Bytes
  /-- `retain_mode`: which half this child shard keeps. -/
  retainMode : RetainMode
  /-- `child_shard_uid`: the child shard's id. -/
  childShardUid : Nat
  deriving Repr, DecidableEq

/-- The result of applying a resharding transition to the parent state
(`chunk_validation.rs:730-733`): the child's new state root and its congestion info. -/
structure ReshardingResult where
  /-- `trie_changes.new_root` — the child trie's root after the split. -/
  newRoot : Bytes
  /-- The child's congestion info after the split and finalization. -/
  congestionInfo : CongestionInfo
  deriving Repr

/-- **The resharding implicit transition**, as the validator computes it: split the parent trie at
the boundary account under the retain mode, and derive the child's congestion info. The parent's
congestion info and buffered totals are inputs (see the module's residual premises for why the
receipt-group reads are not modelled here).

The root is computed from the split trie, not copied from the parent: the child's state root is
whatever the retained subtree hashes to. An empty child (nothing retained) hashes to the validator's
`Trie::EMPTY_ROOT`, taken here from `D2.Trie.emptyRoot` (32 zero bytes) rather than re-derived. -/

def reshardingTransition (parentTrie : PTrie) (parent : CongestionInfo)
    (buffered : BufferedTotals) (p : ReshardingParams) (ownIndex : Nat) : ReshardingResult :=
  let ranges := intervalsToNibbles (boundaryAccountToIntervals p.boundaryAccount p.retainMode)
  { newRoot := NearSpecV3.D2.rootHash (retainRanges parentTrie [] ranges)
    congestionInfo := childCongestionInfo parent p.retainMode buffered p.childShardUid ownIndex }

/-- The child's new state root for a split: retain the parent trie's subtrees inside the ranges and
hash the result. This is `trie_changes.new_root` of the validator's resharding transition, and it is
independent of the congestion bookkeeping. -/
def splitRoot (parentTrie : PTrie) (boundaryAccount : Bytes) (mode : RetainMode) : Bytes :=
  NearSpecV3.D2.rootHash
    (retainRanges parentTrie [] (intervalsToNibbles (boundaryAccountToIntervals boundaryAccount mode)))

/-- `reshardingTransition`'s root is `splitRoot`: the split's state root is the retained trie's hash,
so a checker can verify a witness's resharding post-state root without recomputing congestion. -/
theorem reshardingTransition_newRoot (t : PTrie) (ci : CongestionInfo) (b : BufferedTotals)
    (p : ReshardingParams) (own : Nat) :
    (reshardingTransition t ci b p own).newRoot = splitRoot t p.boundaryAccount p.retainMode := rfl

/-! ## Directed tests on the retained ranges

These decide concrete cases in the kernel, so an edit that changes the split's key classes breaks a
named test. The facts asserted are the ones the pinned Rust unit test
(`resharding.rs:345-404`) asserts about `boundary_account_to_intervals`. -/

private def alice : Bytes := [97, 108, 105, 99, 101]  -- "alice"

/-- A left-retained account column keeps `[col, col‖boundary)`: strictly below the boundary. -/
example : splitKeyInterval 0 alice .left = [([0], [0, 97, 108, 105, 99, 101])] := by decide
/-- A right-retained account column keeps `[col‖boundary, col+1)`: at or above the boundary. -/
example : splitKeyInterval 0 alice .right = [([0, 97, 108, 105, 99, 101], [1])] := by decide
/-- The left range is exactly the lower half of the column and the right the upper half; together
they are the whole column and they do not overlap. -/
example : (splitKeyInterval 2 alice .left).head!.1 = [2] ∧
          (splitKeyInterval 2 alice .left).head!.2 = (splitKeyInterval 2 alice .right).head!.1 ∧
          (splitKeyInterval 2 alice .right).head!.2 = [3] := by decide
/-- A copy-to-both column is the whole column for either mode. -/
example : copyToBothInterval 7 = [([7], [8])] ∧ copyToBothInterval 18 = [([18], [19])] := by decide
/-- A copy-to-one-child column is the whole column for the left child and absent for the right. -/
example : copyToOneChildInterval 13 .left = [([13], [14])] ∧ copyToOneChildInterval 13 .right = [] := by
  decide
/-- The account columns are exactly the 12 pinned ones (`trie_key.rs:89-102`). -/
example : (accountColumns.map (·.id)) = [0, 1, 2, 3, 4, 5, 6, 9, 12, 20, 22, 23] := by decide
/-- The copy-to-both columns are the 6 pinned ones (`resharding.rs:56-64`). -/
example : (copyToBothColumns.map (·.id)) = [7, 10, 11, 15, 18, 19] := by decide
/-- The copy-to-one-child columns are the 4 pinned ones (`resharding.rs:65-73`). -/
example : (copyToOneChildColumns.map (·.id)) = [13, 14, 16, 17] := by decide
/-- The split's three classes plus the two shard-global singletons cover all 22 columns; nothing in
`ALL_COLUMNS_WITH_NAMES` is unhandled. -/
example : splitColumns.length = 22 := by decide

/-! ## Directed tests on the retain decision

`retain_decision` (`resharding.rs:265-290`) on the shapes the Rust comment calls out: "if key is
`a` and interval is `ab`..`cd`, subtree may contain both `aa` which must be excluded and `ac` which
must be retained." -/

/-- A key that is a strict prefix of a range start descends: its subtree straddles the boundary. -/
example : retainDecision [1] [([1, 2], [1, 3])] = .descend := by decide
/-- A key well inside a range retains the whole subtree. -/
example : retainDecision [1, 2, 5] [([1, 2], [1, 3])] = .retainAll := by decide
/-- A key outside every range discards the whole subtree. -/
example : retainDecision [9] [([1, 2], [1, 3])] = .discardAll := by decide
/-- A key equal to the range end is outside it (half-open intervals). -/
example : retainDecision [1, 3] [([1, 2], [1, 3])] = .descend := by decide
/-- With no ranges at all, everything is discarded — the split retains nothing. -/
example : retainDecision [0] [] = .discardAll := by decide

/-! ## Directed tests on the child congestion info -/

private def ci : CongestionInfo :=
  { delayedReceiptsGas := 100, bufferedReceiptsGas := 40, receiptBytes := 20, allowedShard := 7 }

/-- The left child inherits the parent's congestion info byte for byte. -/
example : childCongestionNotFinalized ci .left ⟨10, 5⟩ = ci := by decide
/-- The right child loses exactly the parent's buffered gas and bytes. -/
example : childCongestionNotFinalized ci .right ⟨10, 5⟩ =
    { delayedReceiptsGas := 100, bufferedReceiptsGas := 30, receiptBytes := 15, allowedShard := 7 } := by
  decide
/-- ... and therefore has zero buffered gas when the buffered total equals the parent's. -/
example : (childCongestionNotFinalized ci .right ⟨40, 20⟩).bufferedReceiptsGas = 0 := by decide
/-- The finalized child's allowed shard is the child's own shard, for either retain mode. -/
example : (childCongestionInfo ci .left ⟨10, 5⟩ 3 1).allowedShard = 3 ∧
          (childCongestionInfo ci .right ⟨10, 5⟩ 4 2).allowedShard = 4 := by decide

/-! ## Which child this shard is (`chain/chain/src/resharding/event_type.rs:48-119`,
`chunk_validation.rs:258-308`)

`ReshardingEventType::from_shard_layout` reads the split map out of the *next* layout and, if
exactly one parent has exactly two children, produces the split's params: parent shard, left and
right child shards and the boundary account. The boundary account is
`boundary_accounts[position of left_child_shard in shard_ids]` — the same index relationship the
account→shard map uses. `get_resharding_transition` then returns `Resharding(boundary, Left, uid)`
when this shard uid is the left child and `Resharding(boundary, Right, uid)` when it is the right
child; a shard that is neither child gets no resharding transition.

These are the derivation steps the checker needs in order to *decide* a resharding chunk instead of
excluding it. -/

/-- The split's parameters, as `ReshardingSplitShardParams` carries them. -/
structure SplitShardParams where
  parentShard : Nat
  leftChild : Nat
  rightChild : Nat
  boundaryAccount : Bytes
  deriving Repr, DecidableEq

/-- The boundary account of a split, read the way `from_shard_layout` reads it: the boundary at the
index at which the left child sits in `shard_ids`. -/
def Layout.splitBoundary (l : Layout) (leftChild : Nat) : Option Bytes :=
  let i := l.shardIds.idxOf leftChild
  l.boundaries[i]?

/-- A split map entry whose child count is neither 1 (a pre-existing split, nothing to do) nor 2
(the split this block performs) is malformed: the validator throws
`"invalid number of children for shard {parent_id}"`. -/
def splitMapMalformed (next : Layout) : Bool :=
  next.splitMap.any fun p => p.2.length != 1 && p.2.length != 2

/-- The split map's two-child entries — the split candidates — as `(parent, [left, right])`. The
validator walks the map and treats each such entry as the split, so counting happens on *this* list,
before any boundary lookup: a candidate whose left child is missing from `shard_ids` is still a
candidate (and makes `from_shard_layout` throw later), not a reason to ignore the entry. -/
def splitCandidates (next : Layout) : List (Nat × List Nat) :=
  next.splitMap.filter fun p => p.2.length == 2

/-- `ReshardingEventType::from_shard_layout` on a V3 layout's split map: at most one parent with
exactly two children, and its params. A split map with two two-child parents is an error
(`"can't perform two reshardings at the same time!"`), not a silent `none`; so is a malformed child
count. No two-child parent at all is the validator's `None`. -/
def splitEventOf (next : Layout) : Except String (Option SplitShardParams) :=
  if splitMapMalformed next then
    .error "invalid: invalid number of children in shard split map"
  else match splitCandidates next with
    | [] => .ok none
    | [(parent, children)] =>
      match children with
      | [l, r] =>
        match next.splitBoundary l with
        | some bd => .ok (some ⟨parent, l, r, bd⟩)
        | none => .error "invalid: shard not found in shard layout"
      | _ => .ok none
    | _ => .error "invalid: can't perform two reshardings at the same time"

/-- `get_resharding_transition`'s decision for this shard, given the layout the block will have and
the number of new chunks already seen in this segment. Returns the retain mode when this shard is a
split child, `none` when it is not (the validator's `None` return). -/
def reshardingTransitionOf (next : Layout) (shardId : Nat) (numNewChunksSeen : Nat) :
    Except String (Option (Bytes × RetainMode)) :=
  if numNewChunksSeen > 0 then .ok none
  else match splitEventOf next with
    | .error e => .error e
    | .ok none => .ok none
    | .ok (some p) =>
      if p.leftChild == shardId then .ok (some (p.boundaryAccount, .left))
      else if p.rightChild == shardId then .ok (some (p.boundaryAccount, .right))
      else .ok none

/-! ### Directional tests

`Except String _` carries no `DecidableEq`, so each test states the *result shape* as a boolean
computed from the outcome. The layout below has shard 1 covering accounts below `[98]`, shard 2
covering `[98]`..`[109)`, shard 3 covering `[109]` and up; parent 4 split into 2 and 3. -/

/-- A V3 layout whose split map records one parent with two children. -/
def splitLayout : Layout :=
  { boundaries := [[98], [109]], shardIds := [1, 2, 3],
    idToIndex := [(1, 0), (2, 1), (3, 2)],
    splitMap := [(4, [2, 3])], lastSplit := some 4, ancestorMap := [(2, [1, 4]), (3, [1, 4])] }

/-- The split's params are recovered. The boundary account is `boundaries[index of the left child]`,
i.e. `[109]`: the first account that belongs to the right child, exactly as
`from_shard_layout` reads it (`shard_ids.position(|id| id == left_child_shard)`). -/
def splitEventIsParams : Bool :=
  match splitEventOf splitLayout with
  | .ok (some q) => q == ⟨4, 2, 3, [109]⟩
  | _ => false

example : splitEventIsParams = true := by decide

/-- The left child gets retain mode Left with the boundary account. -/
def leftChildMode : Bool :=
  match reshardingTransitionOf splitLayout 2 0 with
  | .ok (some q) => q == ([109], .left)
  | _ => false

example : leftChildMode = true := by decide

/-- The right child gets retain mode Right. -/
def rightChildMode : Bool :=
  match reshardingTransitionOf splitLayout 3 0 with
  | .ok (some q) => q == ([109], .right)
  | _ => false

example : rightChildMode = true := by decide

/-- A shard that is not a child of the split gets no transition. -/
def nonChildNoTransition : Bool :=
  match reshardingTransitionOf splitLayout 1 0 with | .ok none => true | _ => false

example : nonChildNoTransition = true := by decide

/-- Once a new chunk has been seen the validator returns no resharding transition. -/
def seenChunkNoTransition : Bool :=
  match reshardingTransitionOf splitLayout 2 1 with | .ok none => true | _ => false

example : seenChunkNoTransition = true := by decide

/-- A layout with no split map has no split event. -/
def noSplitMapNoEvent : Bool :=
  match splitEventOf { splitLayout with splitMap := [] } with | .ok none => true | _ => false

example : noSplitMapNoEvent = true := by decide

/-- Two splits in one layout are rejected, matching the validator's error. -/
def twoSplitsRejected : Bool :=
  match splitEventOf { splitLayout with splitMap := [(4, [2, 3]), (5, [6, 7])] } with
  | .error e => e == "invalid: can't perform two reshardings at the same time"
  | _ => false

example : twoSplitsRejected = true := by decide

/-- A parent with three children is malformed. -/
example : splitMapMalformed { splitLayout with splitMap := [(4, [2, 3, 5])] } = true := by decide

end NearSpecV3
