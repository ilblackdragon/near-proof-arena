import NearSpecV3.D2.Types

/-!
# `NearSpecV3.Successor.Routing` — receipt routing across layout changes

`Rcpt.targetShard` (`D2/Types.lean`) routes a distribution receipt to its explicit target. After a
split that target can be a shard the current layout no longer has: a distribution forwarded by a
parent-layout chunk, delayed in the parent's queue (both children inherit it) or buffered towards the
parent by another shard. nearcore resolves such a target to its descendant in the current layout
(`Receipt::receiver_shard_id`, `core/primitives/src/receipt.rs:438-462`, via
`ShardLayout::resolve_to_current_shard`, `shard_layout/mod.rs:228-237`, `v3.rs:315-326`). The successor
paths use `Rcpt.routedShard` below; the signed definition is unchanged, and differs only for targets
outside the layout, which the signed path never decides (`c.same_layout`).
-/

namespace NearSpecV3

/-- `ShardLayoutV3::resolve_to_current_shard` (`v3.rs:315-326`): the shard itself when it is in the
layout, else the first child of its split-map entry, followed through every generation of the split
history; `none` when the shard is in neither. Each step consumes one generation of the finite split
map, so `splitMap.length + 1` steps suffice for an acyclic map (an authenticated layout's). -/
def Layout.resolveV3Fuel (l : Layout) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, s =>
    if l.shardIds.contains s then some s
    else match l.splitMap.find? (·.1 == s) with
      | some (_, c :: _) => l.resolveV3Fuel fuel c
      | _ => none

/-- `ShardLayout::resolve_to_current_shard` for a V3 layout. For V2 only a current shard resolves:
the V2 static split map is not decoded (`decodeLayout`). -/
def Layout.resolveCurrent (l : Layout) (s : Nat) : Option Nat :=
  if l.lastSplit.isNone then (if l.shardIds.contains s then some s else none)
  else l.resolveV3Fuel (l.splitMap.length + 1) s

end NearSpecV3

namespace NearSpecV3.D2
open NearSpecV3

/-- `Receipt::receiver_shard_id` with resolution. An unresolvable target keeps its id, which is then
outside the layout; `StorageExecution.globalTarget` rejects it, as nearcore's
`EpochError::ShardingError` does. -/
def Rcpt.routedShard (r : Rcpt) (layout : Layout) : Nat :=
  match r.body with
  | .distribution d =>
    if layout.shardIds.contains d.target then d.target
    else (layout.resolveCurrent d.target).getD d.target
  | _ => layout.shardOf r.recv

theorem Rcpt.routedShard_of_mem (r : Rcpt) (layout : Layout)
    (h : ∀ d, r.body = .distribution d → layout.shardIds.contains d.target = true) :
    r.routedShard layout = r.targetShard layout := by
  unfold Rcpt.routedShard Rcpt.targetShard
  cases hb : r.body <;> simp_all

end NearSpecV3.D2
