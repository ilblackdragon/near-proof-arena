/-!
# `NearSpecV3.Successor.LayoutReach` — which layout changes a PV86 claim can contain

The resharding checker (`Successor.ReshardCore`) decides a layout change only when the new layout is
V3 (a dynamic split) and the genesis-capable path keeps `c.same_layout`. Every claim epoch must be
PV86 (`c.pv86`). This module records why those exclusions never meet an honest witness, as a small
transcription of how nearcore assigns a layout to an epoch, with the source citations
(nearcore 2.13.4, `44f7ae6c`):

* `EpochManager::next_next_shard_layout` (`chain/epoch-manager/src/lib.rs:679-745`) computes the
  layout of epoch `N+2` when epoch `N` is finalized: the static layout of `config(pv(N+2))` if that
  config is static; else the layout of `N+1` if `config(pv(N))` is not dynamic; else
  `derive_v3(next layout, boundary)` (a V3 layout, `shard_layout/v3.rs`) when the last block of `N`
  carries a `shard_split` for a shard of the next layout, and the layout of `N+1` otherwise.
* `config(pv)` is the epoch config store's entry with the highest version `≤ pv`
  (`core/primitives/src/epoch_manager.rs:527-535`). For mainnet the entries are
  `res/epoch_configs/mainnet/{29,…,81,85,143}.json`; `85.json` has no `shard_layout` and a
  `dynamic_resharding_config`, so `config(86)` is dynamic.
* the genesis epoch's config must be static (`chain/epoch-manager/src/genesis.rs:64-69`, for every
  genesis protocol version other than 29; mainnet and testnet use 29), and the epoch after it reuses
  the genesis epoch info (`lib.rs:942-952`).

Consequences, proved below on that transcription:

1. `no_v2_change_of_dynamic`: if `config(86)` is dynamic, a layout change between two PV86 epochs
   produces a V3 layout. So `ReshardCore`'s `out of domain (c.layout): V2 layout change` is
   unreachable for an honest PV86 claim under the pinned mainnet parameters.
2. `genesis_segment_one_layout`: a segment that reaches the genesis block contains a block of every
   epoch from the genesis epoch to the witness epoch, all PV86 by `c.pv86`; then the genesis
   protocol version is 86, `config(86)` is static, and every one of those epochs has the genesis
   layout. So the genesis path's `c.same_layout` never excludes an honest claim.

Protocol-version facts (UQ-009) are outside this model and are argued in `ReshardCore`'s module
documentation: under 2.13.4 mainnet never had a PV85 epoch.
-/

namespace NearSpecV3.Successor.LayoutReach

/-- The layout part of an epoch config (`ShardLayoutConfig`, `epoch_manager.rs:60-95`). -/
inductive LayoutConfig (L : Type) where
  | static (layout : L)
  | dynamic

/-- `next_next_shard_layout` (`lib.rs:679-745`). `cur` is `config(pv(N))`, `nn` is
`config(pv(N+2))`, `next` the layout of `N+1`, and `derived` the `derive_v3` result when the last
block of `N` selects a split of a shard of `next` (`none` when it does not). -/
def nextNextLayout {L : Type} (cur nn : LayoutConfig L) (next : L) (derived : Option L) : L :=
  match nn with
  | .static l => l
  | .dynamic =>
    match cur with
    | .static _ => next
    | .dynamic => derived.getD next

/-- A chain's epoch sequence (`i` = epoch height): protocol versions, layouts, the split result of
each finalized epoch, and the config store. `step` is `finalize_epoch` storing the layout of `i+2`;
`genesis` is the genesis epoch's static layout, used for epochs 0 and 1. -/
structure Chain (L : Type) where
  cfg : Nat → LayoutConfig L
  pv : Nat → Nat
  layout : Nat → L
  derived : Nat → Option L
  step : ∀ i, layout (i + 2) = nextNextLayout (cfg (pv i)) (cfg (pv (i + 2))) (layout (i + 1)) (derived i)
  genesis0 : cfg (pv 0) = .static (layout 0)
  genesis1 : layout 1 = layout 0

/-- **A layout change between PV86 epochs is a dynamic (V3) split** when `config(86)` is dynamic and
`derive_v3` yields V3 layouts. -/
theorem no_v2_change_of_dynamic {L : Type} (ch : Chain L) (isV3 : L → Prop)
    (hdyn : ch.cfg 86 = .dynamic) (hderive : ∀ i l, ch.derived i = some l → isV3 l)
    (i : Nat) (h0 : ch.pv i = 86) (h2 : ch.pv (i + 2) = 86) :
    ch.layout (i + 2) = ch.layout (i + 1) ∨ isV3 (ch.layout (i + 2)) := by
  rw [ch.step i, h0, h2, hdyn]
  simp only [nextNextLayout]
  cases hd : ch.derived i with
  | none => left; rfl
  | some l => right; exact hderive i l hd

/-- **A genesis segment has one layout.** If every epoch from the genesis epoch to epoch `w` is
PV86, then all of them have the genesis layout. -/
theorem genesis_segment_one_layout {L : Type} (ch : Chain L) (w : Nat)
    (hpv : ∀ i, i ≤ w → ch.pv i = 86) : ∀ i, i ≤ w → ch.layout i = ch.layout 0 := by
  have hs : ch.cfg 86 = .static (ch.layout 0) := by
    have := ch.genesis0; rwa [hpv 0 (Nat.zero_le _)] at this
  intro i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => exact ch.genesis1
  | j + 2, hj =>
    rw [ch.step j, hpv (j + 2) hj, hs]
    rfl

end NearSpecV3.Successor.LayoutReach
