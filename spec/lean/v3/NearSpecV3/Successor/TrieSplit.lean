import NearSpecV3.D2.Trie
import NearSpecV3.ClaimV3

/-!
# `NearSpecV3.Successor.TrieSplit` — `find_trie_split` and the dynamic-resharding split gate

The chunk producer of a shard whose epoch config enables dynamic resharding recomputes, for a chunk
that may be the last of the epoch, whether its shard should be split and where
(`compute_proposed_split`, `chain/chain/src/runtime/mod.rs:583-621`, on the *pre-state* trie of the
chunk, `:284-292`). The result is the chunk header's `proposed_split`, which the validator compares
with its own recomputation (`InvalidChunkHeaderShardSplit`). The claim carries the gate's inputs as a
trusted fact (`apply_facts[].split_gate`, present exactly when the feature, the epoch config, the
last-block condition and `can_reshard` hold, `oracle/v3/src/claim.rs:176-193`).

`check_dynamic_resharding` (`runtime/mod.rs:1731-1769`) and `find_trie_split`
(`core/store/src/trie/split.rs:590-601`, the `TrieDescent` of `:270-560`) are transcribed here:

* the descent walks the four account-keyed subtrees (`ACCOUNT`, `CONTRACT_CODE`, `ACCESS_KEY`,
  `CONTRACT_DATA`) simultaneously, nibble by nibble, choosing at each step the child at which the
  accumulated `memory_usage` crosses half of the total (`find_middle_child`), and keeps the best split
  among the even-length paths that are valid account ids, either at the path itself or with the
  suffix `-0` (`best_split_at_current_path`);
* every node it reads must be in the witness (the recorded storage): a missing node is the
  validator's storage error, which fails the chunk application;
* every other `FindSplitError` (no root, a split path that is not an account id, no first child when
  the path must be extended to an even length, no split found) makes the proposal `None`
  (`compute_proposed_split` logs it and returns `Ok(None)`).

Arithmetic is on `Nat`. The validator's `u64` subtractions in `node_memory_usage` and `descend_step`
cannot underflow on a trie whose stored `memory_usage` values are consistent (each node's value is its
own cost plus its children's), which the node hashes commit to.
-/

namespace NearSpecV3.Successor.TrieSplit
open NearSpec NearSpecV3

def missingNode : String := "invalid: MissingTrieValue (find_trie_split)"

/-- `TrieDescentStage` (`split.rs:63-82`). -/
inductive Stage where
  | cutOff
  | atLeaf (mem : Nat)
  | insideExt (mem : Nat) (rem : List Nat) (child : Option PTrie)
  | atBranch (mem : Nat) (kids : Kids)

/-- `TrieDescentStage::from(GenericTrieNodeWithSize)` (`split.rs:84-111`). -/
def Stage.ofNode : PTrie → Except String Stage
  | .hash _ => throw missingNode
  | .leaf k _ m => pure (if k.isEmpty then .atLeaf m else .insideExt m k none)
  | .ext k c m => pure (.insideExt m k (some c))
  | .branch _ cs m => pure (.atBranch m cs)

def memOf (t : PTrie) : Except String Nat :=
  match t.mem? with
  | some m => pure m
  | none => throw missingNode

def Stage.subtreeMem : Stage → Nat
  | .cutOff => 0
  | .atLeaf m | .insideExt m _ _ | .atBranch m _ => m

/-- `children_memory_usage` (`split.rs:192-222`): 16 entries. -/
def Stage.childrenMem : Stage → Except String (List Nat)
  | .cutOff | .atLeaf _ => pure (List.replicate 16 0)
  | .insideExt m rem child => do
    let n := rem.headD 0
    let v ← match child, rem.length with
      | some c, 1 => memOf c
      | _, _ => pure m
    pure ((List.replicate 16 0).set n v)
  | .atBranch _ cs => (List.range 16).mapM fun i =>
      match cs.at i with
      | some c => memOf c
      | none => pure 0

/-- `node_memory_usage` (`split.rs:134-156`). -/
def Stage.nodeMem (s : Stage) : Except String Nat :=
  match s with
  | .atLeaf m => pure m
  | .atBranch m _ => do
    let cm ← s.childrenMem
    pure (m - cm.foldl (· + ·) 0)
  | .insideExt m rem (some c) =>
    if rem.length == 1 then do pure (m - (← memOf c)) else pure 0
  | _ => pure 0

/-- `descendant_mem_usage` (`split.rs:159-187`). -/
def Stage.descendantMem : Stage → List Nat → Except String Nat
  | s, [] => pure s.subtreeMem
  | .insideExt m rem _, ns => pure (if isPrefix ns rem then m else 0)
  | .atBranch _ cs, n :: rest => do
    match cs.at n with
    | some c => (← Stage.ofNode c).descendantMem rest
    | none => pure 0
  | _, _ => pure 0

def Stage.canDescend : Stage → Bool
  | .insideExt .. | .atBranch .. => true
  | _ => false

def Stage.canDescendNibble (s : Stage) (n : Nat) : Bool :=
  match s with
  | .insideExt _ rem _ => rem.head? == some n
  | .atBranch _ cs => (cs.at n).isSome
  | _ => false

def Stage.firstChild : Stage → Option Nat
  | .insideExt _ rem _ => rem.head?
  | .atBranch _ cs => (Kids.present cs 0).head?.map (·.1)
  | _ => none

/-- `descend` (`split.rs:247-276`). -/
def Stage.descend (s : Stage) (n : Nat) : Except String Stage :=
  match s with
  | .cutOff | .atLeaf _ => pure .cutOff
  | .insideExt m rem child =>
    if rem.head? != some n then pure .cutOff
    else match rem.tail, child with
      | [], none => pure (.atLeaf m)
      | [], some c => Stage.ofNode c
      | r, ch => pure (.insideExt m r ch)
  | .atBranch _ cs =>
    match cs.at n with
    | some c => Stage.ofNode c
    | none => pure .cutOff

/-- `TrieDescent` (`split.rs:283-300`). -/
structure Descent where
  stages : List Stage
  nibbles : List Nat
  left : Nat
  right : Nat
  middle : Nat

def Descent.accounts (d : Descent) : Stage := d.stages.headD .cutOff

def Descent.total (d : Descent) : Nat := d.left + d.right + d.middle

def Descent.currentNodesMem (d : Descent) : Except String Nat :=
  d.stages.foldlM (fun acc s => do pure (acc + (← s.nodeMem))) 0

def Descent.aggregate (d : Descent) : Except String (List Nat) :=
  d.stages.foldlM (fun (acc : List Nat) s => do
    let cm ← s.childrenMem
    pure ((acc.zip cm).map fun (a, b) => a + b)) (List.replicate 16 0)

/-- `find_middle_child` (`split.rs:562-585`). -/
def findMiddleChild (cm : List Nat) (threshold : Nat) : Option (Nat × Nat) := Id.run do
  let mut left := 0
  for i in List.range 16 do
    let c := cm.getD i 0
    if left + c > threshold then return some (i, left)
    left := left + c
  for i in (List.range 16).reverse do
    let c := cm.getD i 0
    if c > 0 then return some (i, left - c)
  return none

def nibblesOfByte (b : Nat) : List Nat := [b / 16, b % 16]

def nibblesToBytes : List Nat → List UInt8
  | a :: b :: rest => UInt8.ofNat (a * 16 + b) :: nibblesToBytes rest
  | _ => []

/-- `near-account-id` 2.0.0 validation (strict rules, `Wasm.validAccountId` on bytes). -/
def validAccountBytes (b : List UInt8) : Bool :=
  if b.length < 2 || b.length > 64 then false
  else Id.run do
    let mut lastSep := true
    for c in b do
      let isSep := c == 0x2D || c == 0x5F || c == 0x2E
      let ok := (0x61 ≤ c && c ≤ 0x7A) || (0x30 ≤ c && c ≤ 0x39) || isSep
      if !ok then return false
      if isSep && lastSep then return false
      lastSep := isSep
    return !lastSep

/-- `nibbles_to_account_id` (`split.rs:603-610`). -/
def accountOf (ns : List Nat) : Option (List UInt8) :=
  if ns.length % 2 != 0 then none
  else
    let b := nibblesToBytes ns
    if validAccountBytes b then some b else none

/-- A split: boundary account, left memory, right memory. -/
abbrev Split := List UInt8 × Nat × Nat

def memDiff (s : Split) : Nat := if s.2.1 ≥ s.2.2 then s.2.1 - s.2.2 else s.2.2 - s.2.1

/-- `attached_data_mem_usage` (`split.rs:432-447`): access keys (separator `col::ACCESS_KEY`) and
contract data (separator `,`). -/
def Descent.attachedMem (d : Descent) : Except String Nat := do
  if (accountOf d.nibbles).isNone then return 0
  let ak ← (d.stages.getD 2 .cutOff).descendantMem (nibblesOfByte 2)
  let cd ← (d.stages.getD 3 .cutOff).descendantMem (nibblesOfByte 44)
  pure (ak + cd)

/-- `best_split_at_current_path` (`split.rs:449-476`); ties keep the first (`min_by_key`). -/
def Descent.bestAtPath (d : Descent) : Except String (Option Split) := do
  let a : Option Split := (accountOf d.nibbles).map fun acct => (acct, d.left, d.right + d.middle)
  let b ← match accountOf (d.nibbles ++ [2, 13, 3, 0]) with   -- "-0"
    | none => pure none
    | some acct => do
      let curr ← d.currentNodesMem
      let att ← d.attachedMem
      pure (some (acct, d.left + curr + att, d.right + d.middle - curr - att))
  pure (match a, b with
    | some x, some y => if memDiff y < memDiff x then some y else some x
    | some x, none => some x
    | none, y => y)

/-- `next_step` (`split.rs:375-410`). -/
def Descent.nextStep (d : Descent) : Except String (Option (Nat × Nat × Nat)) := do
  if !d.accounts.canDescend then return none
  let curr ← d.currentNodesMem
  if d.left + curr > d.total / 2 then return none
  let threshold := d.total / 2 - d.left - curr
  let cm ← d.aggregate
  match findMiddleChild cm threshold with
  | none => return none
  | some (i, lm) =>
    if !d.accounts.canDescendNibble i then return none
    return some (i, cm.getD i 0, lm)

/-- `descend_step` (`split.rs:493-517`). -/
def Descent.descendStep (d : Descent) (n childMem leftMem : Nat) : Except String Descent := do
  let parent ← d.currentNodesMem
  let stages ← d.stages.mapM (·.descend n)
  pure { stages, nibbles := d.nibbles ++ [n], left := d.left + leftMem + parent,
         right := d.right + (d.middle - leftMem - childMem - parent), middle := childMem }

def better (cur : Option Split) (best : Option Split) : Option Split :=
  match cur, best with
  | some c, some b => if memDiff c < memDiff b then some c else some b
  | some c, none => some c
  | none, b => b

/-- `find_trie_split`: `.ok none` for every non-storage `FindSplitError`. -/
def findTrieSplit (root : PTrie) : Except String (Option Split) := do
  let init ← [0, 1, 2, 9].mapM fun k => do
    let s ← Stage.ofNode root
    let s ← s.descend (k / 16)
    s.descend (k % 16)
  let mut d : Descent := { stages := init, nibbles := [], left := 0, right := 0,
                           middle := init.foldl (fun a s => a + s.subtreeMem) 0 }
  let mut best : Option Split := none
  for _ in List.range 256 do
    match ← d.nextStep with
    | none => break
    | some (n, cm, lm) =>
      d ← d.descendStep n cm lm
      best := better (← d.bestAtPath) best
  if d.nibbles.length % 2 != 0 then
    let cm ← d.aggregate
    match d.accounts.firstChild with
    | none => return none   -- FindSplitError::Key
    | some f =>
      d ← d.descendStep f (cm.getD f 0) ((cm.take f).foldl (· + ·) 0)
      best := better (← d.bestAtPath) best
  return best

/-- borsh `TrieSplit { boundary_account, left_memory, right_memory }`. -/
def encodeSplit (s : Split) : Bytes := u32 s.1.length ++ s.1 ++ u64 s.2.1 ++ u64 s.2.2

/-- `check_dynamic_resharding` (`runtime/mod.rs:1731-1769`) on the pre-state trie, given the gate;
`none` when there is no gate (`compute_proposed_split` returns `None` before it). The encoded split is
what the chunk header's `proposed_split` must equal. -/
def expectedProposedSplit (gate : Option SplitGate) (numShards shard : Nat) (preTrie : PTrie)
    (emptyPre : Bool) : Except String (Option Bytes) := do
  let some g := gate | return none
  -- total_mem_usage: no root is a logged error, a missing root node a storage error
  if emptyPre then return none
  let memUsage ← memOf preTrie
  if numShards ≥ g.maxNumberOfShards then return none
  if g.forceSplitShards.contains shard then
    return (← findTrieSplit preTrie).map encodeSplit
  if g.blockSplitShards.contains shard then return none
  if memUsage < g.memoryUsageThreshold then return none
  match ← findTrieSplit preTrie with
  | none => return none
  | some s =>
    if s.2.1 < g.minChildMemoryUsage || s.2.2 < g.minChildMemoryUsage then return none
    return some (encodeSplit s)

end NearSpecV3.Successor.TrieSplit
