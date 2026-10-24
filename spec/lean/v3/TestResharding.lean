import NearSpecV3.Resharding
import NearSpecV3.Successor.Config

/-!
# Whole-model tests for the shard-split semantics (`NearSpecV3.Resharding`)

`Resharding.lean` implements the validator's resharding implicit transition. This module checks it
against the facts the pinned Rust source states, in the same three layers the Rust code is split
into:

1. **The retained ranges** (`boundary_account_to_intervals`, `resharding.rs:33-91`). The Rust unit
   test `test_boundary_account_to_intervals` (`resharding.rs:345-404`) asserts the exact interval
   list for boundary account `alice.near` in both retain modes. Those assertions are reproduced here
   as data checks, so an edit that changes a column's handling class breaks a named check.
2. **The retain decision** (`retain_decision`, `resharding.rs:265-290`), including the case the Rust
   comment calls out by name: key `a` against interval `ab..cd`.
3. **The child congestion info** (`get_child_congestion_info`, `manager.rs:297-383`), whose two
   branches the Rust comments state in words ("left child ... identical congestion info", "right
   child ... subtracting the parent's buffered receipts"), plus the zero-buffered invariant the
   validator asserts.

Every expectation is derived from the Rust source and its unit test, not from the Lean
implementation. Nothing here claims agreement with nearcore on a real split trie: that needs
validator-generated fixtures, which W11's success criterion requires and this module does not
provide.
-/

open NearSpecV3 NearSpec

namespace NearSpecV3.ReshardingTest

/-! ## The pinned Rust unit test's expected intervals

`test_boundary_account_to_intervals` uses `alice.near` as the boundary account and asserts a
specific interval per column. The two lists below are that test's expectations, transcribed. -/

/-- `"alice.near"` as bytes. -/
def alice : Bytes := [97, 108, 105, 99, 101, 46, 110, 101, 97, 114]

/-- The left intervals the Rust test asserts, in `ALL_COLUMNS_WITH_NAMES` order. The 12
account-prefixed columns are `[col, col‖alice)`, the 6 copy-to-both columns are `[col, col+1)`, and
the 4 copy-to-one-child columns are `[col, col+1)`. -/
def expectedLeft : List (Bytes × Bytes) :=
  [ ([0], [0] ++ alice), ([1], [1] ++ alice), ([2], [2] ++ alice), ([3], [3] ++ alice),
    ([4], [4] ++ alice), ([5], [5] ++ alice), ([6], [6] ++ alice),
    ([7], [8]),
    ([9], [9] ++ alice),
    ([10], [11]), ([11], [12]),
    ([12], [12] ++ alice),
    ([13], [14]), ([14], [15]),
    ([15], [16]), ([16], [17]), ([17], [18]),
    ([18], [19]), ([19], [20]),
    ([20], [20] ++ alice),
    ([22], [22] ++ alice), ([23], [23] ++ alice) ]

/-- The right intervals: the 12 account-prefixed columns are `[col‖alice, col+1)`, the 6
copy-to-both columns are `[col, col+1)`, and the 4 copy-to-one-child columns are absent. -/
def expectedRight : List (Bytes × Bytes) :=
  [ ([0] ++ alice, [1]), ([1] ++ alice, [2]), ([2] ++ alice, [3]), ([3] ++ alice, [4]),
    ([4] ++ alice, [5]), ([5] ++ alice, [6]), ([6] ++ alice, [7]),
    ([7], [8]),
    ([9] ++ alice, [10]),
    ([10], [11]), ([11], [12]),
    ([12] ++ alice, [13]),
    ([15], [16]),
    ([18], [19]), ([19], [20]),
    ([20] ++ alice, [21]),
    ([22] ++ alice, [23]), ([23] ++ alice, [24]) ]

/-! ## Layer 1: the retained ranges -/

def intervalChecks : List (String × Bool) :=
  [ ("left: 22 intervals, one per handled column",
      (boundaryAccountToIntervals alice .left).length == 22),
    ("right: 18 intervals, the 4 buffered columns dropped",
      (boundaryAccountToIntervals alice .right).length == 18),
    ("left: intervals equal the Rust unit test's expectation",
      boundaryAccountToIntervals alice .left == expectedLeft),
    ("right: intervals equal the Rust unit test's expectation",
      boundaryAccountToIntervals alice .right == expectedRight),
    -- the split point is the boundary account, byte-lexicographically
    ("left: ACCOUNT(0) splits at the boundary account",
      splitKeyInterval 0 alice .left = [([0], [0] ++ alice)]),
    ("right: ACCOUNT(0) starts at the boundary account",
      splitKeyInterval 0 alice .right = [([0] ++ alice, [1])]),
    -- the two halves of one column are adjacent and cover the whole column
    ("account column halves meet at the boundary",
      (splitKeyInterval 2 alice .left).head!.2 == (splitKeyInterval 2 alice .right).head!.1),
    ("left half starts at the column, right half ends at col+1",
      (splitKeyInterval 2 alice .left).head!.1 == [2] ∧
      (splitKeyInterval 2 alice .right).head!.2 == [3]),
    -- copy-to-both: identical for both modes, whole column
    ("copy-to-both is the whole column, either mode",
      copyToBothInterval 7 == [([7], [8])] ∧
      (boundaryAccountToIntervals alice .left).contains ([18], [19]) ∧
      (boundaryAccountToIntervals alice .right).contains ([18], [19])),
    -- copy-to-one-child: left only
    ("copy-to-one-child present for left",
      copyToOneChildInterval 13 .left == [([13], [14])] ∧
      (boundaryAccountToIntervals alice .left).contains ([13], [14])),
    ("copy-to-one-child absent for right",
      copyToOneChildInterval 13 .right == [] ∧
      !(boundaryAccountToIntervals alice .right).any (fun r => r.1.head? == some 13)),
    -- the three classes are disjoint and cover the pinned 22 columns
    ("the three column classes are disjoint",
      (accountColumns.map (·.id)).all (fun i => !(copyToBothColumns.map (·.id)).contains i) &&
      (accountColumns.map (·.id)).all (fun i => !(copyToOneChildColumns.map (·.id)).contains i) &&
      (copyToBothColumns.map (·.id)).all (fun i => !(copyToOneChildColumns.map (·.id)).contains i)),
    ("the split covers all 22 pinned columns", splitColumns.length == 22) ]

/-! ## Layer 2: the retain decision -/

/-- The Rust comment's own example: key `a` (nibble [1]) against interval `ab..cd`
(nibbles [1,2]..[1,3]) must descend, because the subtree may hold `aa` (excluded) and `ac`
(retained). -/
def decisionChecks : List (String × Bool) :=
  [ ("a strict prefix of a range start descends",
      retainDecision [1] [([1, 2], [1, 3])] == .descend),
    ("a key strictly inside a range retains the subtree",
      retainDecision [1, 2, 5] [([1, 2], [1, 3])] == .retainAll),
    ("a key past every range discards the subtree",
      retainDecision [9] [([1, 2], [1, 3])] == .discardAll),
    ("the range end is outside the half-open interval",
      retainDecision [1, 3] [([1, 2], [1, 3])] == .descend),
    ("the range start itself is a boundary prefix, so it descends",
      retainDecision [1, 2] [([1, 2], [1, 3])] == .descend),
    ("no ranges discards everything",
      retainDecision [0] [] == .discardAll),
    -- a key that is a prefix of the END also descends
    ("a prefix of the range end descends",
      retainDecision [1, 2] [([9, 9], [1, 2, 4])] == .descend),
    -- disjoint range: the key's subtree cannot contain it
    ("a key in a disjoint range retains",
      retainDecision [5] [([1, 2], [1, 3]), ([4], [6])] == .retainAll) ]

/-! ## Layer 3: the child congestion info -/

/-- A parent shard's congestion info with non-zero buffered state. -/
def parentInfo : CongestionInfo :=
  { delayedReceiptsGas := 1_000, bufferedReceiptsGas := 400, receiptBytes := 200, allowedShard := 7 }

/-- The parent's buffered totals as the split reads them. -/
def buffered : BufferedTotals := { gas := 100, bytes := 50 }

/-- The split's derivation and retention checks: the split map yields the validator's params, each
child gets its retain mode, a non-child gets none, and the split's root is the retained subtree's
hash. -/
def splitChecks : List (String × Bool) :=
  [ ("the split map yields the validator's params",
      match splitEventOf splitLayout with
      | .ok (some q) => q == ⟨4, 2, 3, [109]⟩
      | _ => false),
    ("the left child retains left",
      match reshardingTransitionOf splitLayout 2 0 with
      | .ok (some q) => q == ([109], .left) | _ => false),
    ("the right child retains right",
      match reshardingTransitionOf splitLayout 3 0 with
      | .ok (some q) => q == ([109], .right) | _ => false),
    ("a shard outside the split gets no transition",
      match reshardingTransitionOf splitLayout 1 0 with | .ok none => true | _ => false),
    ("a seen new chunk suppresses the transition",
      match reshardingTransitionOf splitLayout 2 1 with | .ok none => true | _ => false),
    ("no split map means no split event",
      match splitEventOf { splitLayout with splitMap := [] } with | .ok none => true | _ => false),
    ("two splits are rejected",
      match splitEventOf { splitLayout with splitMap := [(4, [2, 3]), (5, [6, 7])] } with
      | .error e => e == "invalid: can't perform two reshardings at the same time" | _ => false),
    ("a three-child parent is malformed",
      splitMapMalformed { splitLayout with splitMap := [(4, [2, 3, 5])] }) ]

/-- The tier wiring checks: resharding is a distinct, widest tier, and the signed tier does not
carry it. These are `decide`d, so a change to the tier's configuration breaks a named test. -/
def tierChecks : List (String × Bool) :=
  [ ("the signed tier does not decide resharding",
      (Successor.Tier.cfg .signed).resharding == false),
    ("the curveHosts tier does not decide resharding",
      (Successor.Tier.cfg .curveHosts).resharding == false),
    ("the resharding tier does decide it",
      (Successor.Tier.cfg .resharding).resharding == true),
    ("the resharding tier keeps every narrower decision",
      (Successor.Tier.cfg .resharding).floats &&
        (Successor.Tier.cfg .resharding).gasCap == some maxGasBurnt &&
        (Successor.Tier.cfg .resharding).genesisMainTransition &&
        (Successor.Tier.cfg .resharding).loadingLimits &&
        (Successor.Tier.cfg .resharding).storageResolution &&
        (Successor.Tier.cfg .resharding).curveHosts),
    ("the resharding tier ranks widest",
      Successor.Tier.rank .resharding > Successor.Tier.rank .curveHosts) ]

/-- The split's exclusion guarantee: a subtree is discarded only when its key is outside every
retained range. Stated on the decision logic, which is what a wrong column class or a wrong range
comparison would break. -/
def exclusionChecks : List (String × Bool) :=
  [ ("a key outside every range is discarded",
      retainDecision [9] [([1, 2], [1, 3])] == .discardAll),
    ("a key inside a range is never discarded",
      retainDecision [1, 2, 5] [([1, 2], [1, 3])] != .discardAll),
    ("every key gets exactly one decision",
      [retainDecision [0] [([1], [2])], retainDecision [1, 2] [([1], [2])],
       retainDecision [9] [([1], [2])]].all (fun d =>
        d == .retainAll || d == .discardAll || d == .descend)) ]

def congestionChecks : List (String × Bool) :=
  [ -- "The left child contains all the delayed and buffered receipts from the parent
    --  so it should have identical congestion info."
    ("left child inherits the parent's congestion info",
      childCongestionNotFinalized parentInfo .left buffered == parentInfo),
    -- "The right child ... has no buffered receipts. Its info needs to be computed by
    --  subtracting the parent's buffered receipts from the parent's congestion info."
    ("right child subtracts buffered gas",
      (childCongestionNotFinalized parentInfo .right buffered).bufferedReceiptsGas == 300),
    ("right child subtracts receipt bytes",
      (childCongestionNotFinalized parentInfo .right buffered).receiptBytes == 150),
    ("right child keeps the parent's delayed gas",
      (childCongestionNotFinalized parentInfo .right buffered).delayedReceiptsGas == 1_000),
    -- the invariant the validator asserts: "The right child does not inherit any buffered
    -- receipts. The congestion info must match this invariant."
    ("right child has zero buffered gas when the total equals the parent's",
      (childCongestionNotFinalized parentInfo .right
        { gas := 400, bytes := 200 }).bufferedReceiptsGas == 0),
    ("right child has zero buffered bytes when the total equals the parent's",
      (childCongestionNotFinalized parentInfo .right
        { gas := 400, bytes := 200 }).receiptBytes == 0),
    -- finalize_allowed_shard: the child's own shard
    ("the finalized child's allowed shard is its own",
      (childCongestionInfo parentInfo .left buffered 3 1).allowedShard == 3 ∧
      (childCongestionInfo parentInfo .right buffered 4 2).allowedShard == 4),
    -- a saturating subtraction never goes negative
    ("an over-large buffered total saturates at zero",
      (childCongestionNotFinalized parentInfo .right
        { gas := 10_000, bytes := 10_000 }).bufferedReceiptsGas == 0) ]

/-! ## Layer 4: the transition record -/

def transitionChecks : List (String × Bool) :=
  let p : ReshardingParams := { boundaryAccount := alice, retainMode := .left, childShardUid := 5 }
  let r := reshardingTransition (.hash [0]) parentInfo buffered p 2
  [ ("the transition reports the child's shard id as its congestion target",
      r.congestionInfo.allowedShard == 5),
    ("the left transition inherits the parent's congestion info",
      r.congestionInfo.bufferedReceiptsGas == parentInfo.bufferedReceiptsGas) ]

/-! ## Nibble conversion -/

def nibbleChecks : List (String × Bool) :=
  [ ("one byte is two nibbles",
      toNibbles [171] == [10, 11]),
    ("two bytes are four nibbles",
      toNibbles [171, 205] == [10, 11, 12, 13]),
    ("an empty key is no nibbles",
      toNibbles [] == []),
    ("the empty interval set maps to the empty nibble set",
      intervalsToNibbles [] == []) ]

def allChecks : List (String × Bool) :=
  intervalChecks ++ decisionChecks ++ exclusionChecks ++ congestionChecks ++
  transitionChecks ++ nibbleChecks ++ splitChecks ++ tierChecks

def main : IO UInt32 := do
  let mut bad := 0
  for (name, ok) in allChecks do
    if !ok then
      bad := bad + 1
      IO.eprintln s!"RESHARDING FAIL: {name}"
  IO.println s!"resharding cases: {allChecks.length} total, {bad} failures"
  return if bad = 0 then 0 else 1

end NearSpecV3.ReshardingTest

def main (_ : List String) : IO UInt32 := NearSpecV3.ReshardingTest.main
