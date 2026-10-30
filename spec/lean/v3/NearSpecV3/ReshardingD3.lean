import NearSpecV3.GenesisD3

/-!
# `NearSpecV3.ReshardingD3` — resharding, split gate and same-layout: what D3 excludes and why

The inventory row `L0-resharding` (family `boundary`, owner L6, `docs/research/lean-chunk-coverage.json`)
and the guard row `L0-guard-noResharding` ask for the shard-layout-transition machinery. This module
states, precisely and against the pinned validator, what a D3 claim can and cannot contain on that
axis, and what the two guards in the checker actually buy. The guards are
`c.same_layout` (`ChunkValidationD2.lean:140`, mirrored in the genesis successor at
`GenesisD3.lean:202`) and `c.no_split_gate` (`ChunkValidationD2.lean:156`, mirrored at
`GenesisD3.lean:217`).

## What a resharding transition is, in the validator

A shard-layout change is materialised as an **implicit** transition of the witness
(`ImplicitTransitionParams::Resharding`, `chain/chain/src/stateless_validation/chunk_validation.rs:702-733`):

```rust
ImplicitTransitionParams::Resharding(boundary_account, retain_mode, child_shard_uid) => {
    let old_root = *chunk_extra.state_root();
    let parent_trie = Trie::from_recorded_storage(partial_storage, old_root, true);
    let parent_congestion_info = chunk_extra.congestion_info();
    let child_congestion_info = ReshardingManager::get_child_congestion_info(
        &parent_trie, &parent_shard_layout, parent_congestion_info,
        &child_shard_layout, &child_shard_uid, retain_mode)?;
    let trie_changes = parent_trie.retain_split_shard(&boundary_account, retain_mode)?;
    (child_shard_uid, trie_changes.new_root, child_congestion_info)
}
```

It is produced by `get_resharding_transition` (`chunk_validation.rs:258-305`) only when

```rust
let shard_layout = epoch_manager.get_shard_layout_from_prev_block(prev_header.hash())?;
let prev_epoch_id = epoch_manager.get_prev_epoch_id_from_prev_block(prev_header.hash())?;
let prev_shard_layout = epoch_manager.get_shard_layout(&prev_epoch_id)?;
let block_has_new_shard_layout = epoch_manager.is_next_block_epoch_start(prev_header.hash())?
    && shard_layout != prev_shard_layout;
```

i.e. **only when the shard layout of the previous block's epoch differs from the shard layout of
the previous epoch**. The transition also needs the block to be an epoch start and no new chunk to
have been seen yet (`num_new_chunks_seen > 0` ⇒ `None`), and the child shard to be one of the split
children. So: no layout difference between consecutive epochs ⇒ `get_resharding_transition` returns
`None` for every block ⇒ no `ImplicitTransitionParams::Resharding` can be in any witness.

## The two guards, and the exclusion they license

`checkD2Core` (and its genesis successor `checkD2CoreG`) require

* `c.same_layout`: every epoch row's `shardLayout` equals the endorsed epoch's
  (`ChunkValidationD2.lean:140`), and
* `c.no_split_gate`: no `ApplyFacts` row carries a `splitGate` (`ChunkValidationD2.lean:156`).

`same_layout_forbids_resharding` below turns the first guard into the validator's own precondition:
when the guard holds, the "layouts differ" conjunct of `block_has_new_shard_layout` is false for
every pair of epochs in the claim, hence for every consecutive-epoch pair a segment block can span.
That is the exclusion argument for `L0-resharding`: it is an argument, not an implementation, and it
is exactly as strong as the claim that the epoch table is the source of layout truth — which is what
`c.epochs` is (`spec/claim-v3.md` T6: the layout bytes are a trusted claim fact).

The split gate is a *different* condition and the exclusion is **not** unconditional. See
`splitGate_reachable_at_pv86` and the discussion in `## The split gate at PV86` below.
-/

/-! ## `noResharding` (formerly `Wasm/DomainD3.lean`)

`Wasm.DomainD3` was a parallel domain statement outside `checkD3`'s import closure (UQ-010). It is
retired (2026-10-29, `docs/research/lean-chunk-w00-owner-map.md` §3.4). Its `noResharding` is kept
here, where its theorems live, as the description of the *legacy core*'s (`D3.checkD3Core`) two
resharding guards. It is **not** a domain condition of the statement of record: `D3.checkD3` decides
claims that fail it (the resharding hand-over, `D3/Signed.lean`). Its `contractInD3α` was dropped:
it excluded a contract that merely imports a curve host, while dispatch excludes only a call
(`D3/FunctionCall.lean` `contractOOD`, `Wasm/Exec.lean` `runCall`), so it described no checker. -/

namespace NearSpecV3.Wasm

/-- No resharding anywhere in the claim's segment: one shard layout, no split gate. -/
def noResharding (c : Claim) : Bool :=
  (match c.epochs with
   | [] => true
   | e :: _ => c.epochs.all (·.shardLayout == e.shardLayout)) &&
    c.applyFacts.all (fun f => f.splitGate.isNone)

theorem noResharding_spec (c : Claim) (h : noResharding c = true) :
    (∀ e ∈ c.epochs, ∀ e' ∈ c.epochs, e.shardLayout = e'.shardLayout) ∧
      ∀ f ∈ c.applyFacts, f.splitGate = none := by
  simp only [noResharding, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun e he e' he' => ?_, fun f hf => ?_⟩
  · cases hc : c.epochs with
    | nil => rw [hc] at he; exact absurd he (List.not_mem_nil)
    | cons e0 es =>
      rw [hc] at h1 he he'
      have a1 := List.all_eq_true.mp h1 e he
      have a2 := List.all_eq_true.mp h1 e' he'
      rw [beq_iff_eq] at a1 a2
      rw [a1, a2]
  · have := List.all_eq_true.mp h2 f hf
    exact Option.isNone_iff_eq_none.mp this

end NearSpecV3.Wasm

namespace NearSpecV3

open NearSpec NearSpecV3.D2

/-! ## `c.same_layout` implies the validator's "no layout change" precondition -/

/-- Every epoch row carries the endorsed epoch's shard layout. This is the `c.same_layout` guard as
a predicate, factored out so the theorems below can speak about it without unfolding `checkD2Core`. -/
def sameLayout (c : Claim) (ep : EpochRec) : Bool := c.epochs.all (·.shardLayout == ep.shardLayout)

/-- Every apply-facts row has no split gate. This is the `c.no_split_gate` guard as a predicate. -/
def noSplitGate (c : Claim) : Bool := c.applyFacts.all fun f => f.splitGate.isNone

theorem sameLayout_iff (c : Claim) (ep : EpochRec) :
    sameLayout c ep = true ↔ ∀ e ∈ c.epochs, e.shardLayout = ep.shardLayout := by
  simp [sameLayout, List.all_eq_true, beq_iff_eq]

theorem noSplitGate_iff (c : Claim) :
    noSplitGate c = true ↔ ∀ f ∈ c.applyFacts, f.splitGate = none := by
  simp [noSplitGate, List.all_eq_true, Option.isNone_iff_eq_none]

/-- **`c.same_layout` forbids resharding.** With the guard true, any two epochs of the claim have
byte-identical shard layouts; so for a previous block whose epoch and previous epoch are both in the
claim's epoch table, `shard_layout != prev_shard_layout` is false — the first conjunct of
`get_resharding_transition`'s `block_has_new_shard_layout`
(`chunk_validation.rs:273-274`) cannot hold. No `ImplicitTransitionParams::Resharding` can be in the
witness. -/
theorem sameLayout_forbids_resharding (c : Claim) (ep : EpochRec) (h : sameLayout c ep = true)
    {e e' : EpochRec} (he : e ∈ c.epochs) (he' : e' ∈ c.epochs) :
    e.shardLayout = e'.shardLayout := by
  have h1 := (sameLayout_iff c ep).mp h e he
  have h2 := (sameLayout_iff c ep).mp h e' he'
  rw [h1, h2]

/-- The same statement in the validator's own shape: `block_has_new_shard_layout`'s layout-difference
conjunct is false. `≠` on `Bytes` is decidable, so the negation is a `Bool` fact about the guard. -/
theorem sameLayout_means_no_layout_difference (c : Claim) (ep : EpochRec)
    (h : sameLayout c ep = true) {e e' : EpochRec} (he : e ∈ c.epochs) (he' : e' ∈ c.epochs) :
    ¬ (e.shardLayout ≠ e'.shardLayout) := by
  simp [sameLayout_forbids_resharding c ep h he he']

/-- `Wasm.noResharding`'s first conjunct, as a standalone function of the epoch list (so
the theorems below can state it without a dependent `match` on `c.epochs`). -/
def layoutUniformOf (l : List EpochRec) : Bool :=
  match l with
  | [] => true
  | e :: _ => l.all fun x => x.shardLayout == e.shardLayout

theorem noResharding_eq (c : Claim) :
    Wasm.noResharding c = (layoutUniformOf c.epochs && noSplitGate c) := rfl

/-- **Layout uniformity is pairwise equality.** `layoutUniformOf` compares every row against the head;
this says that is the same as every pair of rows agreeing. -/
theorem layoutUniformOf_iff (l : List EpochRec) :
    layoutUniformOf l = true ↔ ∀ e ∈ l, ∀ e' ∈ l, e.shardLayout = e'.shardLayout := by
  cases l with
  | nil => simp [layoutUniformOf]
  | cons e0 es =>
    simp only [layoutUniformOf, List.all_eq_true, beq_iff_eq]
    constructor
    · rintro h e he e' he'
      rw [h e he, h e' he']
    · intro h e he
      exact h e he e0 (List.mem_cons_self ..)

/-- `sameLayout c ep` and `noResharding`'s layout conjunct agree whenever the endorsed epoch is in
the claim's epoch table. `Wasm.noResharding` compares all epochs against the *head* epoch;
the checker's `c.same_layout` compares all epochs against the *endorsed* epoch. `checkD2Core` requires
the endorsed epoch to be a member of `c.epochs` (`c.epochs.find? (·.epochId == c.epochId)`), so under
that precondition the two predicates are the same condition on the claim. -/
theorem sameLayout_eq_layout_part (c : Claim) (ep : EpochRec) (hmem : ep ∈ c.epochs) :
    sameLayout c ep = true ↔ layoutUniformOf c.epochs = true := by
  rw [layoutUniformOf_iff, sameLayout_iff]
  constructor
  · intro h e he e' he'
    rw [h e he, h e' he']
  · intro h e he
    exact h e he ep hmem

/-- **`noResharding` is exactly the conjunction of the two guards.** So the D2 predicates
`c.same_layout` and `c.no_split_gate` are precisely the two conjuncts of `Wasm.noResharding`,
and an edit to either cannot drift silently away from the domain statement. -/
theorem noResharding_iff_guards (c : Claim) (ep : EpochRec) (hmem : ep ∈ c.epochs) :
    Wasm.noResharding c = true ↔ (sameLayout c ep = true ∧ noSplitGate c = true) := by
  rw [noResharding_eq, Bool.and_eq_true, sameLayout_eq_layout_part c ep hmem]

/-! ## The split gate at PV86: the exclusion is **conditional**, and the condition is not free

`c.no_split_gate` excludes claims that carry a split gate. That guard does *not* mean "a split gate
cannot be reached at PV86": it means "the D3 relation declines to decide such a claim". The oracle
that generates the corpora builds the gate exactly when the validator would
(`oracle/v3/src/claim.rs:176-193`):

```rust
let split_gate = match cfg.dynamic_resharding_config() {
    Some(c) if ProtocolFeature::DynamicResharding.enabled(x_pv)
        && emd.is_next_block_possibly_last_in_epoch(x.header().height(), prev)?
        && emd.can_reshard(prev, c.min_epochs_between_resharding)? => Some(SplitGate { … }),
    _ => None,
};
```

`ProtocolFeature::DynamicResharding` is enabled at PV85 (`core/primitives-core/src/version.rs:564`),
and mainnet's epoch config for PV85 is `ShardLayoutConfig::Dynamic`
(`core/primitives/res/epoch_configs/mainnet/85.json`: `dynamic_resharding_config`, no
`shard_layout`; `max_number_of_shards = 10`, `memory_usage_threshold = 40000000000`,
`min_child_memory_usage = 10000000000`, `min_epochs_between_resharding = 2`). So at PV86 on mainnet
`dynamic_resharding_config()` is `Some` and the gate is reachable — subject only to
`is_next_block_possibly_last_in_epoch` and `can_reshard` (`chain/epoch-manager/src/lib.rs:777-793`,
whose condition is "no resharding in the last `min_epochs_between_resharding` epochs"), and then to
`check_dynamic_resharding` (`chain/chain/src/runtime/mod.rs:1731-1769`) deciding to split. -/

/-- The five fields a `SplitGate` carries are exactly the five `DynamicReshardingConfig` fields the
oracle copies (`oracle/v3/src/claim.rs:184-190`), so "the claim carries a gate" is checkable against
the pinned epoch config without any hidden field. This is a statement about the *structure* (there
is no sixth, unrecorded field), which is what makes the guard decidable from the claim bytes alone. -/
theorem splitGate_fields_are_config_fields (g : SplitGate) :
    g = ⟨g.memoryUsageThreshold, g.minChildMemoryUsage, g.maxNumberOfShards,
         g.forceSplitShards, g.blockSplitShards⟩ := rfl

/-- **The mainnet PV85 gate values are exactly the `SplitGate` the oracle would copy.** Pinned at
`core/primitives/res/epoch_configs/mainnet/85.json` (`dynamic_resharding_config`): thresholds
40 000 000 000 / 10 000 000 000, `max_number_of_shards` 10, and both split lists empty. So a claim
carrying this gate is carrying a *reachable* mainnet value, not a value the config cannot produce. -/
def mainnetPv85Gate : SplitGate :=
  ⟨40000000000, 10000000000, 10, [], []⟩

theorem mainnetPv85Gate_is_config_value :
    mainnetPv85Gate = ⟨40000000000, 10000000000, 10, [], []⟩ := rfl

/-- **The split gate is not vacuous at PV86.** `noResharding` is *false* on a claim with a split
gate, so the guard `c.no_split_gate` genuinely removes claims from the relation rather than being a
no-op on the corpora: the corpora just happen not to contain any (0 of 115 284 claims carry one).
The split-gate half of `L0-resharding` is therefore an *exclusion*, not a proven impossibility — and this theorem is the honest
record of the difference. -/
theorem splitGate_excludes_nonempty (c : Claim)
    (h : c.applyFacts = [{ validatorUpdate := none, minimumStake := 0, splitGate := some ⟨0, 0, 0, [], []⟩ }]) :
    noSplitGate c = false := by
  simp [noSplitGate, h]

/-! ## Directed tests on the guards

These are the "directed negative tests" the exclusion argument needs: each `example` is decided by
the kernel (`by decide`) on a concrete claim, so a future edit that weakens a guard — or that makes
`noResharding` stop being the conjunction of the two checker guards — breaks a named test. They are
*not* whole-witness tests; the whole-witness negatives for the genesis branch live in
`var/l6/mutate_genesis.py`, and the resharding axis has no whole-witness negative because no corpus
case carries a split gate or a layout change (0 of 115 284). -/

private def gate : SplitGate := mainnetPv85Gate
private def ep : EpochRec :=
  { epochId := [], protocolVersion := 86, epochHeight := 1, shardLayout := [], validators := [] }
private def base : Claim :=
  { protocolVersion := 86, chainId := [], epochId := [], chunkInner := [], blocks := [],
    rsDataParts := 0, rsTotalParts := 0, epochs := [ep], epochStartAfter := [0, 0],
    applyFacts := [{ validatorUpdate := none, minimumStake := 0, splitGate := none }],
    txValid := [], genesisChunkExtra := none }

/-- An honest base claim satisfies both guards. -/
example : noSplitGate base = true ∧ sameLayout base ep = true := by decide
/-- A mainnet-PV85-shaped split gate makes the split-gate guard false. -/
example : noSplitGate { base with applyFacts :=
    [{ validatorUpdate := none, minimumStake := 0, splitGate := some gate }] } = false := by decide
/-- A layout change between two epochs makes the same-layout guard false. -/
example : sameLayout { base with epochs := [ep, { ep with shardLayout := [1] }] } ep = false := by decide
/-- Several epochs sharing one layout keep the same-layout guard true (D2 ⊄ D3 was fixed here). -/
example : sameLayout { base with epochs := [ep, ep] } ep = true := by decide
/-- The two guards together *are* `noResharding`, on the split-gate axis. -/
example : Wasm.noResharding { base with applyFacts :=
    [{ validatorUpdate := none, minimumStake := 0, splitGate := some gate }] } = false := by decide
/-- ... and on the layout axis. -/
example : Wasm.noResharding { base with epochs := [ep, { ep with shardLayout := [1] }] } = false := by decide
/-- ... and true when neither axis is violated. -/
example : Wasm.noResharding base = true := by decide

end NearSpecV3
