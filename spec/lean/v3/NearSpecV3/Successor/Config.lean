import NearSpecV3.ChallengeChunkV3Gas
import NearSpecV3.ChallengeChunkV3Float
import NearSpecV3.GenesisD3
import NearSpecV3.Successor.RuntimeCore
import NearSpecV3.Successor.ReshardCore
import NearSpecV3.D3.Signed

/-!
# W00 interface 1/7 — the canonical checker and its tiers

This module publishes the **single semantic root** of the successor checker plus its explicit
protocol configuration and tier predicates. It is additive: it defines no new semantics of its own,
it names the configurations that already exist as adapters (`checkD3`, `checkD3F`,
`checkD3Proto`, `checkD3ProtoFloat`, `checkD3G`) and composes the two configurations that have no
existing adapter (`genesis + floats + protocol gas`) and the recorder-backed runtime.

## What is signed and what is not

`checkD3`, `RelD3`, `D3.gAlpha` and the oracle pins are the **signed** statement. Its widenings
toward nearcore are accepted as strengthenings (UQ-010, `docs/research/lean-chunk-w00-owner-map.md`
§3.2–§3.4). `checkSuccessor` is a *successor* dispatcher: at the signed configuration
(`signedRecordCfg`) it is definitionally the signed checker (`checkSuccessor_signed` below is `rfl`),
at `signedCfg` it is the signed checker's legacy core `D3.checkD3Core` (`checkSuccessor_signedCore`),
and every broader tier is a different configuration of the same root.

## The configuration

`ProtocolCfg` is the complete, explicit configuration of one successor run:

* `protocolVersion` — the protocol version whose runtime parameters the checker assumes. Only 86 is
  implemented; any other value is an explicit, classified exclusion (`checkSuccessor_unsupported_pv`),
  not a silent reinterpretation under PV86 parameters. Settling mixed-epoch / activation-segment
  configurations is UQ-009 (owner L9 + L6) and is **not** done here.
* `floats` — `NearCfg.floats` (`Wasm.floatPv86` when true). L2 owns the float kernel and its tests.
* `gasCap` — the per-chunk function-call gas bound. `some D3.gAlpha` is the signed prover-capacity
  bound; `some maxGasBurnt` is the bound the narrower successor tiers inherit from
  `ChallengeChunkV3Gas`; `none` is nearcore's behaviour — `max_gas_burnt` (1 Pgas at PV86,
  `runtime_configs/83.yaml:7`) bounds one function call, not a chunk, and a chunk whose last receipt
  starts below the gas limit can burn more than 1 Pgas of function-call gas. `.allFeatures` (the
  Gate-B tier) uses `none`; UQ-012 asks whether a stated `G_α` contract is acceptable for any other.
* `genesisMainTransition` — use L6's genesis-aware validation pipeline.
* `storageResolution` — use the recorder-backed main transition and runtime identifier resolution.
  The legacy merged-value overestimate is disabled; the 8 MiB serialized witness cap remains
  unless `witnessUnbounded` (set on `.allFeatures`).

`ProtocolCfg.wasm` is the derived `NearCfg`. It is deliberately a *function* of `floats` and `loadingLimits`, so a
configuration cannot carry an arbitrary `NearCfg` that drifts from the declared protocol version.

## Tiers and their predicates

`Tier` names successor configurations. Their feature sets are not a linear inclusion chain. `Tier.cfg` is its configuration and
`Tier.checker` its checker. The **tier predicate** is `Tier.domainPredicate`: the tier's declared
domain, as a decidable predicate on the *verdict* — a tier excludes an input exactly when its checker
classifies it as `out of domain`. This is the honest form of the predicate for a successor: the
*declared* domain is "everything the tier decides"; the complement is "the exclusions the tier still
carries", and each exclusion is a named obligation in the W00 owner map
(`docs/research/lean-chunk-w00-owner-map.md`).

## Residual premises

* The `genesis + floats + protocol-gas` composition (`checkD3GProtoFloat`) has a 1,788-case
  verdict replay checkpoint. This is not full observable or representative-window validation.
* loadingLimits selects the pinned x86-64 Wasmtime pooling instance-layout correction.
  runtimeLimits combines it with genesis, floats and protocol gas. This is a semantic correction,
  not a theorem that the old and new runtime agree on every byte input.
* No theorem here states that any successor tier agrees with nearcore. Agreement is a differential
  obligation (W13/W14), not a property of this module.
* `checkSuccessor` does not implement the "one semantic root" as a *refinement* of the signed
  relation. It is a dispatch table over configurations; refinement is W12's obligation.
-/

namespace NearSpecV3.Successor

open NearSpec NearSpecV3

/-! ## Protocol configuration -/

/-- The explicit configuration of one successor run. Every field is a protocol decision or a
prover-capacity decision that the signed statement leaves implicit; nothing is defaulted silently. -/
structure ProtocolCfg where
  /-- Protocol version whose parameters are assumed. Only 86 is implemented (UQ-009). -/
  protocolVersion : Nat := 86
  /-- `NearCfg.floats`: decide float contracts instead of excluding them (L2's `floatPv86`). -/
  floats : Bool := false
  /-- Per-chunk function-call gas bound: `some D3.gAlpha` (signed), `some maxGasBurnt` (narrower
  successor tiers), or `none` (nearcore's behaviour: no per-chunk bound; `.allFeatures`). -/
  gasCap : Option Nat := some D3.gAlpha
  /-- Use L6's genesis-aware pipeline (`checkD2CoreG`) instead of `checkD2Core`. -/
  genesisMainTransition : Bool := false
  /-- Pinned validator's Wasmtime pooling allocation failure semantics. `signedCfg` sets it (it is
  part of `Wasm.pv86`, and so of `checkD3`); the field default stays `false`. -/
  loadingLimits : Bool := false
  /-- Chunk-scoped proof recording and runtime contract identifier resolution. -/
  storageResolution : Bool := false
  /-- Opt-in typed global actions, distribution receipts and promise translation. -/
  globalActions : Bool := false
  /-- Complete-code witness relation: the cold resolution with witness bytes hash-checked
  explicitly (`CodeResolution.complete_eq_cold`). Reads no compiled cache. -/
  completeCodeWitness : Bool := false
  /-- Opt-in `D3γ` curve-host dispatch: decide the 14 curve host functions (`ecrecover`,
  `p256_verify`, `alt_bn128_*`, `bls12381_*`) instead of excluding a contract that imports or calls
  one. The signed configuration keeps this `false`, so the signed statement's surface is unchanged
  (`checkSuccessor_signed` stays `rfl`). -/
  curveHosts : Bool := false
  /-- Opt-in resharding: decide a claim whose epochs differ in shard layout, or whose facts carry a
  split gate, by applying the split's trie retention and checking the child's post-state root. The
  signed configuration keeps this `false`, so both `c.same_layout` and `c.no_split_gate` stay in
  force there and `checkSuccessor_signed` remains `rfl`. -/
  resharding : Bool := false
  /-- Opt-in lift of the `c.blocks.length ≤ 32` chain-segment bound. That bound is a prover-capacity
  restriction inherited from D0 (Gate B forbids it as an accepted configuration), not a protocol
  condition; the pipeline already walks an arbitrary `c.blocks` list. The signed configuration keeps
  this `false`, so the bound stays in force there and `checkSuccessor_signed` remains `rfl`. -/
  segmentUnbounded : Bool := false
  /-- Opt-in lift of the `|state_witness| ≤ 8 MiB` witness bound (`w.size`), the D0 witness-capacity
  choice. nearcore's own 64 MiB decode bound is kept by the witness decoder on every configuration.
  The signed configuration keeps this `false`. -/
  witnessUnbounded : Bool := false
  /-- Opt-in lift of the `numShards ≤ 64` half of `c.layout`, the D0 routing-table size. nearcore
  has no such limit. The signed configuration keeps this `false`. -/
  layoutUnbounded : Bool := false
  /-- Observation only (W01): record failure kinds, per-outcome compute and per-receipt storage
  attribution (`NearCfg.observeDetail`). Set by the driver's `--emit-full` / `--blind-full`; no
  check reads what it records. -/
  observeDetail : Bool := false
  /-- UQ-010 (2026-10-29): outside the legacy pipeline's two preconditions (one shard layout and no
  split check; storage-proof limits never reached), decide a legacy error with the recorder engine at
  this configuration's Wasm configuration and no per-chunk gas cap (`withReshardHandover`, `D3/Signed.lean`). Only the signed
  statement of record sets it (`signedRecordCfg`); the narrower legacy tiers keep the exclusions,
  and the whole-state tiers never take the legacy branch. -/
  reshardHandover : Bool := false

/-- The Wasm configuration of this protocol run. A function of `floats` and `loadingLimits`: the successor does not
admit an arbitrary `NearCfg` that could drift from the declared protocol version. -/
def ProtocolCfg.wasm (cfg : ProtocolCfg) : Wasm.NearCfg :=
  let base := if cfg.floats then Wasm.floatPv86 else Wasm.pv86
  { base with loadingLimits := cfg.loadingLimits, globalActions := cfg.globalActions, curveHosts := cfg.curveHosts,
              observeDetail := cfg.observeDetail }

/-- The signed configuration: exactly `checkD3`'s arguments. `loadingLimits := true` because
`Wasm.pv86` carries the pinned instance-loading rule (signed-tier valid-reject fixes 2026-10-27);
every tier built from `signedCfg` inherits it, so `.runtimeLimits` now differs from
`.genesisFloatsProtoGas` in name only. -/
def signedCfg : ProtocolCfg := { loadingLimits := true }

/-- The signed statement of record: `signedCfg` (whose checker is the legacy core `D3.checkD3Core`)
with the UQ-010 hand-over (`D3.checkD3`, `D3/Signed.lean`). Every other tier is still built from
`signedCfg`; the narrower legacy tiers keep the legacy exclusions, and the whole-state tiers never take
the legacy branch. -/
def signedRecordCfg : ProtocolCfg := { signedCfg with reshardHandover := true }

/-- The signed configuration with resharding decided. -/
def reshardingCfg : ProtocolCfg := { signedCfg with resharding := true }

/-- The protocol gas bound as a configuration (`L1`'s successor bound). -/
def protocolGasCfg : ProtocolCfg := { signedCfg with gasCap := some maxGasBurnt }

/-! ## Verdicts and tier predicates -/

/-- The three-way classification of a checker run. `outOfDomain` is a *declared exclusion*, not a
reject: it says the tier declines to decide the input. -/
inductive Verdict where
  | accept
  | reject (reason : String)
  | outOfDomain (reason : String)
  deriving DecidableEq, Repr

/-- `"out of domain"` as a byte list, used to classify a checker's error string without relying on
`String.startsWith` (which would pull `Classical.choice` into a relation if this were used there;
this module only classifies verdicts, but the same discipline keeps the axiom audit trivial). -/
def oodPrefix : List Char := "out of domain".toList

/-- Classify an error string as an exclusion when it starts with `"out of domain"`. -/
def isExclusion (e : String) : Bool := e.toList.take oodPrefix.length == oodPrefix

/-- Classify a checker result. Total: every result, including every error, has a verdict. -/
def Verdict.ofExcept : Except String Unit → Verdict
  | .ok _ => .accept
  | .error e => if isExclusion e then .outOfDomain e else .reject e

/-- The checker's verdict on an input. Total by construction: every input produces a verdict. -/
def checkVerdict (f : Bytes → Bytes → Except String Unit) (c w : Bytes) : Verdict :=
  Verdict.ofExcept (f c w)

/-- A verdict is *in domain* unless the checker reported an exclusion. This is the tier predicate's
decidable form: `true` means "this tier decides the input". -/
def Verdict.inDomain : Verdict → Bool
  | .outOfDomain _ => false
  | .accept => true
  | .reject _ => true

/-- The exclusion reason, when the tier excluded the input. -/
def Verdict.exclusionReason : Verdict → Option String
  | .outOfDomain r => some r
  | _ => none

/-! ## The single root -/

/-- The genesis-aware, float-aware, protocol-gas-aware composition that has no existing adapter.
Defined here (a new file) rather than by editing `GenesisD3.lean` or `ChallengeChunkV3Float.lean`. -/
def checkD3GProtoFloat (claimBytes witnessBytes : Bytes) : Except String Unit :=
  checkD2CoreG (D3.d3Hooks Wasm.floatPv86) true claimBytes witnessBytes (some maxGasBurnt)

/-- `RelD3GProtoFloat`: the relation of the composed genesis/float/gas configuration. No differential
evidence exists for this composition; it is offered as a successor entry point only. -/
def RelD3GProtoFloat (claimBytes witnessBytes : Bytes) : Prop :=
  checkD3GProtoFloat claimBytes witnessBytes = .ok ()

/-- The classified exclusion for a protocol configuration this successor does not implement. -/
def unsupportedPvError (pv : Nat) : String :=
  "out of domain (c.pv86): successor configuration assumes protocol version " ++ toString pv ++
  ", only 86 is implemented"

/-- **The single semantic root.** One dispatcher over the explicit protocol configuration. Every
tier's checker is this function at that tier's configuration; there is no second dispatch path. -/
def checkSuccessor (cfg : ProtocolCfg) (claimBytes witnessBytes : Bytes) : Except String Unit :=
  match cfg.protocolVersion with
  | 86 =>
    let codePolicy : CodeWitnessPolicy :=
      if cfg.completeCodeWitness then .complete else .coldPartial
    let baseDriver : ExecutionDriver :=
      if cfg.resharding then reshardingDriver cfg.wasm cfg.globalActions codePolicy
      else recorderDriver cfg.wasm cfg.globalActions codePolicy
    let mkDriver : ExecutionDriver :=
      { baseDriver with segmentUnbounded := cfg.segmentUnbounded,
                        witnessUnbounded := cfg.witnessUnbounded,
                        layoutUnbounded := cfg.layoutUnbounded }
    if cfg.resharding && !segmentHasGenesis claimBytes then
      -- the resharding tiers read a segment across layout boundaries (`ReshardCore`)
      checkReshardCore mkDriver (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
    else if cfg.storageResolution || cfg.globalActions || cfg.completeCodeWitness || cfg.resharding then
      if cfg.genesisMainTransition then
        checkD2CoreGWith mkDriver (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
      else
        checkD2CoreWith mkDriver (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
    else if cfg.genesisMainTransition then
      if cfg.reshardHandover then
        withReshardHandover cfg.wasm
          (checkD2CoreG (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap)
          claimBytes witnessBytes
      else
        checkD2CoreG (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
    else if cfg.reshardHandover then
      withReshardHandover cfg.wasm
        (checkD2Core (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap)
        claimBytes witnessBytes
    else
      checkD2Core (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
  | _ => .error (unsupportedPvError cfg.protocolVersion)

/-- The whole-state driver `checkSuccessor` builds for a wide configuration. -/
def successorDriver (cfg : ProtocolCfg) : ExecutionDriver :=
  let codePolicy : CodeWitnessPolicy :=
    if cfg.completeCodeWitness then .complete else .coldPartial
  let baseDriver : ExecutionDriver :=
    if cfg.resharding then reshardingDriver cfg.wasm cfg.globalActions codePolicy
    else recorderDriver cfg.wasm cfg.globalActions codePolicy
  { baseDriver with segmentUnbounded := cfg.segmentUnbounded,
                    witnessUnbounded := cfg.witnessUnbounded,
                    layoutUnbounded := cfg.layoutUnbounded }

/-- The computed outputs of a wide configuration's non-genesis transition. With `blind = false` it
runs every check `checkSuccessor` runs on a non-genesis claim (the genesis-capable path delegates
such claims to `checkD2CoreWith`, the projection of this function) and returns what it computed.
With `blind = true` the comparisons against produced values are skipped (`blindOutputs`), so inputs
whose output fields are zeroed still yield the computed outputs. A genesis claim is reported out of
domain here; narrow (non-whole-state) configurations are not supported. -/
def checkSuccessorObs (cfg : ProtocolCfg) (blind : Bool) (claimBytes witnessBytes : Bytes) :
    Except String Observable :=
  match cfg.protocolVersion with
  | 86 =>
    if cfg.resharding then
      checkReshardCoreObs { successorDriver cfg with blindOutputs := blind } (D3.d3Hooks cfg.wasm) true
        claimBytes witnessBytes cfg.gasCap
    else if cfg.storageResolution || cfg.globalActions || cfg.completeCodeWitness || cfg.resharding then
      checkD2CoreWithObs { successorDriver cfg with blindOutputs := blind } (D3.d3Hooks cfg.wasm) true
        claimBytes witnessBytes cfg.gasCap
    else .error "out of domain (outputs): only whole-state successor tiers emit outputs"
  | _ => .error (unsupportedPvError cfg.protocolVersion)

/-- The successor relation of a configuration. -/
def RelSuccessor (cfg : ProtocolCfg) (claimBytes witnessBytes : Bytes) : Prop :=
  checkSuccessor cfg claimBytes witnessBytes = .ok ()

/-- The successor checker as a boolean mirror. -/
def acceptsSuccessor (cfg : ProtocolCfg) (claimBytes witnessBytes : Bytes) : Bool :=
  match checkSuccessor cfg claimBytes witnessBytes with
  | .ok () => true
  | .error _ => false

/-! ## Old signed entry points, preserved definitionally -/

/-- At the signed configuration the root **is** `checkD3`: not a reimplementation and not a theorem
about a reimplementation, but the same term. -/
theorem checkSuccessor_signed (c w : Bytes) : checkSuccessor signedRecordCfg c w = D3.checkD3 c w := rfl

/-- At `signedCfg` (no hand-over) the root is the legacy core `D3.checkD3Core`. -/
theorem checkSuccessor_signedCore (c w : Bytes) :
    checkSuccessor signedCfg c w = D3.checkD3Core c w := rfl

/-- Consequently the signed relation is preserved definitionally. -/
theorem relSuccessor_signed_iff (c w : Bytes) : RelSuccessor signedRecordCfg c w ↔ D3.RelD3 c w := Iff.rfl

/-- And the signed boolean mirror. -/
theorem acceptsSuccessor_signed (c w : Bytes) :
    acceptsSuccessor signedRecordCfg c w = D3.acceptsD3 c w := rfl


/-- `"out of domain"` prefixed to any string is classified as an exclusion. -/
theorem isExclusion_prefix (s : String) : isExclusion ("out of domain" ++ s) = true := by
  simp [isExclusion, oodPrefix, String.toList_append]

/-- A configuration for a protocol version other than 86 is an explicit exclusion; it never falls
back to PV86 parameters. -/
theorem checkSuccessor_unsupported_pv (cfg : ProtocolCfg) (c w : Bytes)
    (h : cfg.protocolVersion ≠ 86) :
    checkSuccessor cfg c w = .error (unsupportedPvError cfg.protocolVersion) ∧
      isExclusion (unsupportedPvError cfg.protocolVersion) = true := by
  have h' : checkSuccessor cfg c w = .error (unsupportedPvError cfg.protocolVersion) := by
    unfold checkSuccessor
    split
    next hpv => exact absurd hpv h
    next _ _ => rfl
  exact ⟨h', by simp [unsupportedPvError, isExclusion, oodPrefix, String.toList_append]⟩

/-! ## Tiers -/

/-- Named configurations. Floats, gas and genesis are independent dimensions; loading limits
correct runtime semantics. Enumeration/rank alone never establishes relation inclusion. -/
inductive Tier where
  | signed
  | floats
  | protoGas
  | floatsProtoGas
  | genesis
  | genesisFloatsProtoGas
  | runtimeLimits
  | storageResolution
  | globalActions
  | completeCodeGlobal
  /-- Every decision the signed tier makes, plus floats, protocol gas, genesis, loading limits,
  storage resolution and the `D3γ` curve-host table. This is the widest tier: it decides a chunk
  that imports or calls a curve host instead of excluding it. -/
  | curveHosts
  /-- Every decision the `curveHosts` tier makes, plus resharding: a claim whose epochs differ in
  shard layout or whose facts carry a split gate is decided by the split's retention instead of
  excluded. -/
  | resharding
  /-- Every implemented feature at once: the whole-state `globalActions` path (typed global actions,
  distribution receipts and promise translation), the `curveHosts` table and resharding together.
  This is the only tier whose domain is the union of the other wide tiers': the named tiers are not
  cumulative (`curveHosts`/`resharding` omit `globalActions`, so each excludes 222 chunks that
  `globalActions` decides). On authenticated witness bytes `completeCodeGlobal` resolves code as
  `globalActions` does (`complete_eq_cold`); until 2026-10-29 it rejected deploy-served code (178
  nearcore-valid STRAT cases). See `allFeatures_sets_globalActions`,
  `allFeatures_sets_curveHosts` and `allFeatures_sets_resharding`. -/
  | allFeatures
  deriving DecidableEq, Repr

/-- The tier's configuration. -/
def Tier.cfg : Tier → ProtocolCfg
  | .signed => signedRecordCfg
  | .floats => { signedCfg with floats := true }
  | .protoGas => protocolGasCfg
  | .floatsProtoGas => { signedCfg with floats := true, gasCap := some maxGasBurnt }
  | .genesis => { signedCfg with genesisMainTransition := true }
  | .genesisFloatsProtoGas =>
    { signedCfg with floats := true, gasCap := some maxGasBurnt, genesisMainTransition := true }

  | .runtimeLimits =>
    { signedCfg with floats := true, gasCap := some maxGasBurnt, genesisMainTransition := true, loadingLimits := true }

  | .storageResolution =>
    { signedCfg with floats := true, gasCap := some maxGasBurnt, genesisMainTransition := true,
                         loadingLimits := true, storageResolution := true }

  | .globalActions =>
    { signedCfg with floats := true, gasCap := some maxGasBurnt, genesisMainTransition := true,
                     loadingLimits := true, storageResolution := true, globalActions := true }
  | .completeCodeGlobal =>
    { signedCfg with floats := true, gasCap := some maxGasBurnt, genesisMainTransition := true,
                     loadingLimits := true, storageResolution := true, globalActions := true,
                     completeCodeWitness := true }
  | .curveHosts =>
    { signedCfg with floats := true, gasCap := some maxGasBurnt, genesisMainTransition := true,
                     loadingLimits := true, storageResolution := true, curveHosts := true }
  | .resharding =>
    { signedCfg with floats := true, gasCap := some maxGasBurnt, genesisMainTransition := true,
                     loadingLimits := true, storageResolution := true, curveHosts := true,
                     resharding := true }
  -- Every implemented feature at once. This is the only tier whose domain is the union of the
  -- other wide tiers': the named tiers are not cumulative (`curveHosts`/`resharding` omit
  -- `globalActions`), and `completeCodeGlobal` is narrower than `globalActions`.
  -- It is also the Gate-B tier: no arena-derived cap remains. `gasCap := none` because nearcore has
  -- no per-chunk function-call gas limit (`max_gas_burnt` is per function call,
  -- `gas_counter.rs:87-101`, and a chunk's last receipt may start below the chunk gas limit and
  -- burn up to `max_total_prepaid_gas`, `runtime/src/lib.rs` `process_receipts`); the 32-block
  -- segment, the 8 MiB witness and the 64-shard layout bounds are lifted (docs/evidence/
  -- lean-chunk-completion/gate-b-caps/README.md).
  | .allFeatures =>
    { signedCfg with floats := true, gasCap := none, genesisMainTransition := true,
                     loadingLimits := true, storageResolution := true, globalActions := true,
                     curveHosts := true, resharding := true, segmentUnbounded := true,
                     witnessUnbounded := true, layoutUnbounded := true }

/-- The tier's checker: the root at the tier's configuration. -/
def Tier.checker (t : Tier) : Bytes → Bytes → Except String Unit := checkSuccessor t.cfg

/-- The tier's relation. -/
def Tier.rel (t : Tier) (c w : Bytes) : Prop := Tier.checker t c w = .ok ()

/-- **The tier predicate.** A tier decides an input unless its checker reports an exclusion. Every
input gets a verdict; "not decided" is itself a classified result. -/
def Tier.domainPredicate (t : Tier) (c w : Bytes) : Bool :=
  (checkVerdict (Tier.checker t) c w).inDomain

/-- The tier's exclusion reason, when it declines the input. -/
def Tier.exclusion (t : Tier) (c w : Bytes) : Option String :=
  (checkVerdict (Tier.checker t) c w).exclusionReason

/-! ## The widest tier's configuration is the composition of the wide ones

The named wide tiers were declared as a rank chain, but the chain is **false as written**: the
`curveHosts` and `resharding` configurations set `curveHosts := true` without `globalActions`, so a
chunk whose *shape* needs the global-action path is excluded there even though `.globalActions`
decides it. Measured on 3,138 nearcore-valid cases: `.globalActions` decides 222 chunks that
`.curveHosts` and `.resharding` exclude, and `.resharding` decides 237 that `.globalActions`
excludes. Neither is wider. `.allFeatures` is the join of both. -/

/-- `.allFeatures` sets every feature field `.globalActions` sets; its gas bound is wider (`none` in
place of `some maxGasBurnt`: nearcore has no per-chunk function-call gas limit). -/
theorem allFeatures_sets_globalActions :
    (Tier.cfg .allFeatures).globalActions = true ∧
      (Tier.cfg .allFeatures).storageResolution = true ∧
      (Tier.cfg .allFeatures).floats = true ∧
      (Tier.cfg .allFeatures).genesisMainTransition = true ∧
      (Tier.cfg .allFeatures).loadingLimits = true ∧
      (Tier.cfg .allFeatures).gasCap = none := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `.allFeatures` sets every field `.curveHosts` sets. -/
theorem allFeatures_sets_curveHosts : (Tier.cfg .allFeatures).curveHosts = true := rfl

/-- `.allFeatures` sets every field `.resharding` sets. -/
theorem allFeatures_sets_resharding : (Tier.cfg .allFeatures).resharding = true := rfl

/-- `.allFeatures` lifts the prover-capacity `c.segment` bound; the signed configuration does not. -/
theorem allFeatures_lifts_segment :
    (Tier.cfg .allFeatures).segmentUnbounded = true ∧ signedCfg.segmentUnbounded = false := ⟨rfl, rfl⟩

/-- `.allFeatures` carries no arena-derived cap: no per-chunk function-call gas bound, and the
8 MiB witness and 64-shard layout bounds are lifted; the signed configuration keeps all of them. -/
theorem allFeatures_lifts_arena_caps :
    (Tier.cfg .allFeatures).gasCap = none ∧
      (Tier.cfg .allFeatures).witnessUnbounded = true ∧
      (Tier.cfg .allFeatures).layoutUnbounded = true ∧
      signedCfg.gasCap = some D3.gAlpha ∧ signedCfg.witnessUnbounded = false ∧
      signedCfg.layoutUnbounded = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `c.segment` lift is additive: at the signed configuration the segment bound is still
enforced, so `checkSuccessor_signed` is untouched. -/
theorem segmentUnbounded_signed_false : (Tier.cfg .signed).segmentUnbounded = false := rfl

/-- The join is *strict*: neither `.globalActions` nor `.resharding` sets both features. -/
theorem wide_tiers_not_cumulative :
    (Tier.cfg .resharding).globalActions = false ∧
      (Tier.cfg .globalActions).resharding = false ∧
      (Tier.cfg .globalActions).curveHosts = false := ⟨rfl, rfl, rfl⟩

/-- `.completeCodeGlobal` adds the complete-code witness policy to `.globalActions`; `.allFeatures`
uses the cold-partial policy. Since 2026-10-29 the two policies resolve every call identically on
authenticated witness bytes (`complete_eq_cold`). The configuration is still not an ancestor of
`.allFeatures` (which does not set the flag); the verdict-level lift is W12's O7. -/
theorem completeCodeGlobal_not_in_join :
    (Tier.cfg .completeCodeGlobal).completeCodeWitness = true ∧
      (Tier.cfg .allFeatures).completeCodeWitness = false := ⟨rfl, rfl⟩

/-- Tiers are ordered by domain inclusion; this is a *declaration*, not a proved refinement. The
refinement obligations are W12's (`relSuccessor_*_mono`), and they need the adapter agreement
theorems below plus the still-missing semantic families.

**The earlier rank order was false.** Measured on the 3,138 nearcore-valid cases Lean refused, the
named tiers are not cumulative: `.curveHosts` and `.resharding` omit `globalActions`, so each
*excludes* 222 chunks its rank-8 predecessor decides; `.completeCodeGlobal` was narrower than
`.globalActions` until 2026-10-29 (its complete-code policy rejected deploy-served code); it now
resolves code as the cold policy does. `.allFeatures` is the first tier that actually composes every
implemented feature; only for it does "higher rank" mean "wider domain" among the wide tiers.
The rank remains a *declaration*. The refinement theorems that are proved (gas bound, genesis
main transition, `c.segment`, the resharding driver on genesis segments) and the obligations that
remain are in `Successor/TierMono.lean`. -/
def Tier.rank : Tier → Nat
  | .signed => 0 | .floats => 1 | .protoGas => 2 | .floatsProtoGas => 3
  | .genesis => 4 | .genesisFloatsProtoGas => 5 | .runtimeLimits => 6 | .storageResolution => 7
  | .globalActions => 8 | .curveHosts => 9 | .resharding => 10 | .allFeatures => 11
  | .completeCodeGlobal => 12

/-! ## The adapters, at their tiers

Each theorem below is `rfl`: the tier's checker is the existing adapter term. That is the contract
W02–W11 rely on when they say "the successor is the same checker with a different configuration". -/

theorem tier_signed_eq_checkD3 (c w : Bytes) :
    Tier.checker .signed c w = D3.checkD3 c w := rfl

theorem tier_floats_eq_checkD3F (c w : Bytes) :
    Tier.checker .floats c w = checkD3F c w := rfl

theorem tier_protoGas_eq_checkD3Proto (c w : Bytes) :
    Tier.checker .protoGas c w = checkD3Proto c w := rfl

theorem tier_floatsProtoGas_eq_checkD3ProtoFloat (c w : Bytes) :
    Tier.checker .floatsProtoGas c w = checkD3ProtoFloat c w := rfl

theorem tier_genesis_eq_checkD3G (c w : Bytes) :
    Tier.checker .genesis c w = checkD3G c w := rfl

theorem tier_genesisFloatsProtoGas_eq (c w : Bytes) :
    Tier.checker .genesisFloatsProtoGas c w = checkD3GProtoFloat c w := rfl

/-- The signed tier's checker is literally `checkD3`, so a successor tier list cannot drift from the
signed entry point without breaking this named theorem. -/
theorem signed_tier_checker_eq (c w : Bytes) :
    Tier.checker .signed c w = D3.checkD3 c w := tier_signed_eq_checkD3 c w

/-- The signed tier's relation is the signed relation. -/
theorem signed_tier_rel_iff (c w : Bytes) : Tier.rel .signed c w ↔ D3.RelD3 c w := Iff.rfl

/-! ## Every input produces a verdict

The root is total on bytes: there is no input for which it returns nothing. The two theorems below
are the W00 "every input produces a result/error" obligation at the checker level; the differential
harness's own totality is interface 7. -/

theorem checkSuccessor_total (cfg : ProtocolCfg) (c w : Bytes) :
    (checkSuccessor cfg c w).isOk = true ∨ ∃ e, checkSuccessor cfg c w = .error e := by
  cases h : checkSuccessor cfg c w with
  | ok u => exact Or.inl rfl
  | error e => exact Or.inr ⟨e, rfl⟩

theorem checkVerdict_total (f : Bytes → Bytes → Except String Unit) (c w : Bytes) :
    ∃ v, checkVerdict f c w = v := ⟨_, rfl⟩

/-! ## Axiom-closure check points

These are deliberately trivial; they exist so an auditor can confirm the module's theorems do not
depend on `sorryAx` or on axioms outside the allowed set. -/

#print axioms checkSuccessor_signed
#print axioms tier_floats_eq_checkD3F
#print axioms checkSuccessor_unsupported_pv

/-! ## W02: the completeness-domain witness bound for `.allFeatures`

`WfClaim.DomainTier` (`ChallengeChunkV3.lean`, a signed file) fixes every tier's completeness
domain to claims with a `Rel_t` witness of at most `maxWitnessChunk` (64 MiB until 2026-10-30, now
75,497,501 bytes: UQ-010 item 6(c)), and its comment
justifies this by "the code blobs total ≤ 4 000 000 bytes". That premise is **false at PV86**: a
cold validator's accessed pre-state contract code is not part of the storage proof and is loaded at
`contract_loading_bytes` ≈ 1.09e6 gas/byte, so one chunk can require on the order of a gigabyte of
distinct code. nearcore bounds it only at the single `ContractCodeResponse` of 64 MiB
(`MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE`), which `.allFeatures` now models as the
`w.code_response_size` exclusion. Consequently a `witness.bin` on `.allFeatures` can hold a
compressed state witness of up to 48 MiB (`near-arena-cwitness-v3`) **and** up to 64 MiB of code
blobs, so a 64 MiB witness bound would exclude real chunks.

The correct completeness-domain witness bound for `.allFeatures` is the sum of the framing, the
compressed-witness cap and the code-response cap below. This is the bound a completeness statement
for `.allFeatures` must use instead of `maxWitnessChunk`. The signed tier's own bound was raised on
2026-10-30 (UQ-010 item 6(c), user decision): a signed `witness.bin` carries the state witness in the
clear (≤ 8 MiB via `w.size`) plus at most one 64 MiB code response, so `maxWitnessChunk` is now
`(4 + 21) + (4 + 8 MiB) + 64 MiB` = 75,497,501 bytes; the 64 MiB bound it replaces could exclude a real
large-code chunk from the signed completeness statement (soundness was never affected). -/
def allFeaturesWitnessBound : Nat :=
  -- 4+22 tag ‖ 4 + compressed state witness (≤ MAX_COMPRESSED_STATE_WITNESS_SIZE)
  -- ‖ code-response Vec<CodeBytes> (≤ MAX_UNCOMPRESSED_CONTRACT_CODE_RESPONSE_SIZE)
  (4 + 22) + 4 + maxCompressedWitnessBytes + maxContractCodeResponseBytes

theorem allFeaturesWitnessBound_exceeds_maxWitnessChunk :
    maxWitnessChunk < allFeaturesWitnessBound := by
  unfold allFeaturesWitnessBound maxCompressedWitnessBytes maxContractCodeResponseBytes maxWitnessChunk
  decide

end NearSpecV3.Successor
