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
`noResharding` is D2's resharding exclusion (`c.same_layout` + `c.no_split_gate`,
`ChunkValidationD2.lean:140, 156`): every epoch of the claim has the byte-identical shard layout
and no apply fact carries a split gate. Segments may span epochs (as in D2), but the layout never
changes, so no resharding transition can be in the witness. (An earlier version also required a
single epoch, which made D3 exclude 825 in-D2 multi-epoch witnesses of the D3 corpus: D2 ⊄ D3.)
`noResharding_spec` states what acceptance guarantees, and the `example`s check that it rejects.

**Contract domain.** Every contract executed in the chunk must prepare inside D3α: no float type
or opcode, which is `prepare … = .outOfDomain`. `contractInD3α` is that predicate as a `Bool`.

**Reconciliation with the statement of record (UQ-010, 2026-10-27).** These predicates are not in
the import closure of any checker; they state the domain, and they must agree with what the
checkers do. Two disagreements are resolved here, in the direction of the checker:

* *Curve hosts.* `contractInD3α` used to reject a contract that merely **imports** a curve host.
  No checker does that: preparation decides floats and defers curve hosts to the call
  (`D3/FunctionCall.lean` `contractOOD`; `Wasm.runCall`, `Wasm/Exec.lean`), so an import-only
  curve contract is accepted by `checkD3` and `checkD3S` and agrees with nearcore. Calling a curve
  host is a run-time event (`out of domain (e.wasm-α): … host function … not modelled`), not a
  property of the contract bytes, so it is not part of this static predicate any more.
* *Resharding.* `noResharding` is the D3α rung's guard (`checkD3`'s `c.same_layout` and
  `c.no_split_gate`, proved equal to it by `ReshardingD3.noResharding_iff_guards`). The statement
  of record `Successor.RelD3S` decides resharding (`Successor/Record.lean`), so `noResharding` is
  not a domain condition of the record; it bounds only the `.d3a` rung.
-/

namespace NearSpecV3.Wasm

open NearSpecV3

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

/-- A contract executed in the chunk is inside D3α: it prepares without a float type or opcode.
Preparation and compile errors are in-domain outcomes (the call fails in nearcore). Curve-host
imports are not excluded here: only a call is, at run time (module docstring). -/
def contractInD3α (cfg : NearCfg) (code : ByteArray) : Bool :=
  match prepare cfg code with
  | .outOfDomain _ => false
  | _ => true

/-- `contractInD3α` is exactly "preparation does not report out of domain". -/
theorem contractInD3α_iff (cfg : NearCfg) (code : ByteArray) :
    contractInD3α cfg code = true ↔ ∀ r, prepare cfg code ≠ .outOfDomain r := by
  unfold contractInD3α
  cases prepare cfg code <;> simp

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
/-- several epochs with one layout are in domain (as in D2) -/
example : noResharding { base with epochs := [ep, ep], epochStartAfter := [0, 1] } = true := by decide
/-- a layout change between epochs (resharding) is rejected -/
example : noResharding { base with epochs := [ep, { ep with shardLayout := [1] }] } = false := by decide

end NearSpecV3.Wasm
