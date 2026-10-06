import NearSpecV3.ClaimV3
import NearSpecV3.Wasm.Exec

/-!
# `InD3α`: the parts decided before execution

`Rel_D3` will be `Rel_D2` (the D1 lane's action/queue model) with WASM function calls. Its domain
predicate `InD3α` is the conjunction of the D2 domain and the conditions below. They are stated
here so that RuntimeD3 can call them directly.

**Resharding is D∞ (outside every D3 stage).** In nearcore a shard-layout change takes effect at
the first block of a new epoch. The witness carries a resharding transition only when the chunk's
block crosses such a boundary (`get_resharding_transition`, `chunk_validation.rs:258-308`; the
witness-level split is `Trie::from_recorded_storage(.., true)` at `chunk_validation.rs:709`).
`noResharding` keeps a claim to one epoch with no epoch start in the segment and no split gate,
which is the same condition D0/D1 use (`ChunkValidationV0.lean:111-129`). So the shard layout is
constant over the segment and no resharding transition can be in the witness.
`noResharding_spec` states what acceptance guarantees, and the `example`s check that it rejects.

**Contract domain.** Every contract executed in the chunk must prepare inside D3α: no float type
or opcode, which is `prepare … = .outOfDomain`. It must also not import any curve host function
(`curveHosts`). The execution layer already reports both as `out-of-domain` (`Exec.runCall`).
`contractInD3α` is the same predicate as a `Bool`.
-/

namespace NearSpecV3.Wasm

open NearSpecV3

/-- No resharding anywhere in the claim's segment: single epoch, no epoch start, no split gate. -/
def noResharding (c : Claim) : Bool :=
  c.epochs.length == 1 && c.epochStartAfter.all (· == 0) &&
    c.applyFacts.all (fun f => f.splitGate.isNone)

theorem noResharding_spec (c : Claim) (h : noResharding c = true) :
    c.epochs.length = 1 ∧ (∀ b ∈ c.epochStartAfter, b = 0) ∧
      ∀ f ∈ c.applyFacts, f.splitGate = none := by
  simp only [noResharding, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- A contract executed in the chunk is inside D3α. -/
def contractInD3α (cfg : NearCfg) (code : ByteArray) : Bool :=
  match prepare cfg code with
  | .outOfDomain _ => false
  | .ok p => !p.m.imports.any (fun i => curveHosts.contains i.name)
  | _ => true   -- preparation/compile errors are in-domain outcomes (the call fails in nearcore)

private def gate : SplitGate :=
  { memoryUsageThreshold := 0, minChildMemoryUsage := 0, maxNumberOfShards := 0,
    forceSplitShards := [], blockSplitShards := [] }
private def ep : EpochRec :=
  { epochId := [], protocolVersion := 86, epochHeight := 1, shardLayout := [], validators := [] }
private def base : Claim :=
  { protocolVersion := 86, chainId := [], epochId := [], chunkInner := [], blocks := [],
    rsDataParts := 0, rsTotalParts := 0, epochs := [ep], epochStartAfter := [0, 0],
    applyFacts := [{ validatorUpdate := none, minimumStake := 0, splitGate := none }],
    txValid := [], genesisChunkExtra := none }

example : noResharding base = true := by decide
/-- a split gate (the resharding trigger) is rejected -/
example : noResharding { base with applyFacts :=
    [{ validatorUpdate := none, minimumStake := 0, splitGate := some gate }] } = false := by decide
/-- an epoch start inside the segment (where a new layout takes effect) is rejected -/
example : noResharding { base with epochStartAfter := [0, 1] } = false := by decide
/-- a second epoch (a layout change between epochs) is rejected -/
example : noResharding { base with epochs := [ep, ep] } = false := by decide

end NearSpecV3.Wasm
