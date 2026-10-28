import NearSpecV3.Successor.ReshardCore

/-!
# `RelD3S`: the statement of record on the successor engine (2026-10-27)

`D3.RelD3` (`checkD3 = checkD2Core (d3Hooks Wasm.pv86) …`) runs the legacy D2 engine. That engine
cannot decide two kinds of valid chunks, so the signed statement excluded or rejected them:

* **resharding** — a claim whose epochs differ in shard layout (`c.same_layout`), or whose apply
  facts carry a split gate (`c.no_split_gate`). Only `ReshardCore` reads a segment across a layout
  change, applies the split's trie retention and recomputes the split gate;
* **the storage-proof limits** — the legacy engine bounds the recorded storage by the merged-value
  overestimate (`w.size: storage-proof upper bound may exceed …`) and does not model the
  per-receipt limit, the chunk soft limit's postponement or the yield-timeout soft check, so it
  rejects valid chunks that nearcore postpones work in (`MissingTrieValue`, measured on
  `storage-limit-fixtures`).

`checkD3S` is the same pipeline the successor tiers run, at the D3α feature set: the recorder engine
(`StorageExecution.run`) behind `reshardingDriver`, `ReshardCore` for every non-genesis segment, and
the genesis-capable shell (`checkD2CoreWith`) otherwise. The Wasm configuration is `Wasm.pv86` with
the pinned instance-loading rule; floats, curve hosts, global actions, ML-DSA keys, the `G_α`
per-chunk gas bound, the 32-block segment, the 8 MiB in-the-clear witness and the 64-shard layout
bound stay the declared D3α exclusions. The witness may be in the clear (`near-arena-witness-v3`)
or compressed as distributed (`near-arena-cwitness-v3`); nearcore's 48 MiB encoded / 64 MiB decoded
limits and the 64 MiB code-response cap (`w.code_response_size`) apply exactly as on `.allFeatures`.

`Successor.Config` proves `checkSuccessor signedCfg = checkD3S` by `rfl`, so the `--tier signed`
checker is this term. `ChallengeChunkV3` adds it as the rung `.d3s` of the challenge relation;
`RelD3` stays the `.d3a` rung, unchanged, so every result stated about `RelD3` (the `zk-formal`
joins, the kernel non-vacuity examples, the reexec artifact) still holds of that rung.
-/

namespace NearSpecV3.Successor

open NearSpec NearSpecV3

/-- The statement of record's Wasm configuration: `Wasm.pv86` with the pinned loading rule, no
floats, no curve hosts, no global actions (the D3α contract domain). -/
def recordWasm : Wasm.NearCfg :=
  { Wasm.pv86 with loadingLimits := true, globalActions := false, curveHosts := false }

/-- The statement of record's driver: the recorder engine with resharding, every arena bound kept. -/
def recordDriver : ExecutionDriver :=
  { reshardingDriver recordWasm false .coldPartial with
    segmentUnbounded := false, witnessUnbounded := false, layoutUnbounded := false }

/-- **The statement of record.** `ReshardCore` on every segment without a genesis block, the
genesis-capable shell otherwise (which reports `c.not_genesis` for a genesis main transition). -/
def checkD3S (claimBytes witnessBytes : Bytes) : Except String Unit :=
  if true && !segmentHasGenesis claimBytes then
    checkReshardCore recordDriver (D3.d3Hooks recordWasm) true claimBytes witnessBytes (some D3.gAlpha)
  else
    checkD2CoreWith recordDriver (D3.d3Hooks recordWasm) true claimBytes witnessBytes (some D3.gAlpha)

/-- The relation of record. -/
def RelD3S (claimBytes witnessBytes : Bytes) : Prop := checkD3S claimBytes witnessBytes = .ok ()

/-- Its boolean mirror. -/
def acceptsD3S (claimBytes witnessBytes : Bytes) : Bool :=
  match checkD3S claimBytes witnessBytes with
  | .ok () => true
  | .error _ => false

theorem relD3S_iff_acceptsD3S (c w : Bytes) : RelD3S c w ↔ acceptsD3S c w = true := by
  unfold RelD3S acceptsD3S
  cases checkD3S c w with
  | ok u => cases u; simp
  | error e => simp

instance (c w : Bytes) : Decidable (RelD3S c w) :=
  decidable_of_iff _ (relD3S_iff_acceptsD3S c w).symm

/-- The engine of record keeps the D3α arena bounds: the 32-block segment, the 8 MiB in-the-clear
witness and the 64-shard layout. -/
theorem recordDriver_bounded :
    recordDriver.segmentUnbounded = false ∧ recordDriver.witnessUnbounded = false ∧
      recordDriver.layoutUnbounded = false := ⟨rfl, rfl, rfl⟩

/-- It decides resharding (the `c.same_layout`/`c.no_split_gate` guards are lifted) and reads the
compressed witness and the code-response cap as nearcore does. -/
theorem recordDriver_features :
    recordDriver.resharding = true ∧ recordDriver.compressedWitness = true ∧
      recordDriver.codeResponseCap = true := ⟨rfl, rfl, rfl⟩

/-- The contract domain of record: no floats, no curve hosts, no global actions, loading limits on. -/
theorem recordWasm_d3α :
    recordWasm.floats = false ∧ recordWasm.curveHosts = false ∧ recordWasm.globalActions = false ∧
      recordWasm.loadingLimits = true := ⟨rfl, rfl, rfl, rfl⟩

end NearSpecV3.Successor
