import NearSpecV3.ChallengeChunkV3Gas
import NearSpecV3.ChallengeChunkV3Float
import NearSpecV3.GenesisD3
import NearSpecV3.Successor.RuntimeCore

/-!
# W00 interface 1/7 — the canonical checker and its tiers

This module publishes the **single semantic root** of the successor checker plus its explicit
protocol configuration and tier predicates. It is additive: it defines no new semantics of its own,
it names the configurations that already exist as adapters (`checkD3`, `checkD3F`,
`checkD3Proto`, `checkD3ProtoFloat`, `checkD3G`) and composes the two configurations that have no
existing adapter (`genesis + floats + protocol gas`) and the recorder-backed runtime.

## What is signed and what is not

`checkD3`, `RelD3`, `D3.gAlpha` and the oracle pins are the **signed** statement and are immutable.
`checkSuccessor` is a *successor* dispatcher: at the signed configuration it is definitionally the
signed checker (`checkSuccessor_signed` below is `rfl`), and every broader tier is a different
configuration of the same root. Nothing here widens `checkD3`.

## The configuration

`ProtocolCfg` is the complete, explicit configuration of one successor run:

* `protocolVersion` — the protocol version whose runtime parameters the checker assumes. Only 86 is
  implemented; any other value is an explicit, classified exclusion (`checkSuccessor_unsupported_pv`),
  not a silent reinterpretation under PV86 parameters. Settling mixed-epoch / activation-segment
  configurations is UQ-009 (owner L9 + L6) and is **not** done here.
* `floats` — `NearCfg.floats` (`Wasm.floatPv86` when true). L2 owns the float kernel and its tests.
* `gasCap` — the per-chunk function-call gas bound. `some D3.gAlpha` is the signed prover-capacity
  bound; `some maxGasBurnt` is the protocol bound from L1's `ChallengeChunkV3Gas`; `none` disables the
  bound (documented as "no per-chunk gas condition" — **not** an accepted configuration, see UQ-012).
* `genesisMainTransition` — use L6's genesis-aware validation pipeline.
* `storageResolution` — use the recorder-backed main transition and runtime identifier resolution.
  The legacy merged-value overestimate is disabled; the serialized witness cap remains.

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
  /-- Per-chunk function-call gas bound: `some D3.gAlpha` (signed), `some maxGasBurnt` (protocol),
  or `none` (no bound; not an accepted configuration, UQ-012). -/
  gasCap : Option Nat := some D3.gAlpha
  /-- Use L6's genesis-aware pipeline (`checkD2CoreG`) instead of `checkD2Core`. -/
  genesisMainTransition : Bool := false
  /-- Pinned validator's Wasmtime pooling allocation failure semantics. -/
  loadingLimits : Bool := false
  /-- Chunk-scoped proof recording and runtime contract identifier resolution. -/
  storageResolution : Bool := false
  /-- Opt-in typed global actions, distribution receipts and promise translation. -/
  globalActions : Bool := false
  /-- Explicit complete-code witness relation, independent of compiled cache history. -/
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

/-- The Wasm configuration of this protocol run. A function of `floats` and `loadingLimits`: the successor does not
admit an arbitrary `NearCfg` that could drift from the declared protocol version. -/
def ProtocolCfg.wasm (cfg : ProtocolCfg) : Wasm.NearCfg :=
  let base := if cfg.floats then Wasm.floatPv86 else Wasm.pv86
  { base with loadingLimits := cfg.loadingLimits, globalActions := cfg.globalActions, curveHosts := cfg.curveHosts }

/-- The signed configuration: exactly `checkD3`'s arguments. -/
def signedCfg : ProtocolCfg := {}

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
      { baseDriver with segmentUnbounded := cfg.segmentUnbounded }
    if cfg.storageResolution || cfg.globalActions || cfg.completeCodeWitness || cfg.resharding then
      if cfg.genesisMainTransition then
        checkD2CoreGWith mkDriver (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
      else
        checkD2CoreWith mkDriver (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
    else if cfg.genesisMainTransition then
      checkD2CoreG (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
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
  { baseDriver with segmentUnbounded := cfg.segmentUnbounded }

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
    if cfg.storageResolution || cfg.globalActions || cfg.completeCodeWitness || cfg.resharding then
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
theorem checkSuccessor_signed (c w : Bytes) : checkSuccessor signedCfg c w = D3.checkD3 c w := rfl

/-- Consequently the signed relation is preserved definitionally. -/
theorem relSuccessor_signed_iff (c w : Bytes) : RelSuccessor signedCfg c w ↔ D3.RelD3 c w := Iff.rfl

/-- And the signed boolean mirror. -/
theorem acceptsSuccessor_signed (c w : Bytes) :
    acceptsSuccessor signedCfg c w = D3.acceptsD3 c w := rfl

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
  `globalActions` decides), and `completeCodeGlobal` is *narrower* than `globalActions` (its
  complete-code policy rejects 76 valid warm-cache chunks). See `allFeatures_sets_globalActions`,
  `allFeatures_sets_curveHosts` and `allFeatures_sets_resharding`. -/
  | allFeatures
  deriving DecidableEq, Repr

/-- The tier's configuration. -/
def Tier.cfg : Tier → ProtocolCfg
  | .signed => signedCfg
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
  | .allFeatures =>
    { signedCfg with floats := true, gasCap := some maxGasBurnt, genesisMainTransition := true,
                     loadingLimits := true, storageResolution := true, globalActions := true,
                     curveHosts := true, resharding := true, segmentUnbounded := true }

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

/-- `.allFeatures` sets every field `.globalActions` sets. -/
theorem allFeatures_sets_globalActions :
    (Tier.cfg .allFeatures).globalActions = true ∧
      (Tier.cfg .allFeatures).storageResolution = true ∧
      (Tier.cfg .allFeatures).floats = true ∧
      (Tier.cfg .allFeatures).genesisMainTransition = true ∧
      (Tier.cfg .allFeatures).loadingLimits = true ∧
      (Tier.cfg .allFeatures).gasCap = some maxGasBurnt := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `.allFeatures` sets every field `.curveHosts` sets. -/
theorem allFeatures_sets_curveHosts : (Tier.cfg .allFeatures).curveHosts = true := rfl

/-- `.allFeatures` sets every field `.resharding` sets. -/
theorem allFeatures_sets_resharding : (Tier.cfg .allFeatures).resharding = true := rfl

/-- `.allFeatures` lifts the prover-capacity `c.segment` bound; the signed configuration does not. -/
theorem allFeatures_lifts_segment :
    (Tier.cfg .allFeatures).segmentUnbounded = true ∧ signedCfg.segmentUnbounded = false := ⟨rfl, rfl⟩

/-- The `c.segment` lift is additive: at the signed configuration the segment bound is still
enforced, so `checkSuccessor_signed` is untouched. -/
theorem segmentUnbounded_signed_false : (Tier.cfg .signed).segmentUnbounded = false := rfl

/-- The join is *strict*: neither `.globalActions` nor `.resharding` sets both features. -/
theorem wide_tiers_not_cumulative :
    (Tier.cfg .resharding).globalActions = false ∧
      (Tier.cfg .globalActions).resharding = false ∧
      (Tier.cfg .globalActions).curveHosts = false := ⟨rfl, rfl, rfl⟩

/-- `.completeCodeGlobal` adds the complete-code witness policy to `.globalActions`, and that policy
is *not* monotone in domain: it rejects valid warm-cache chunks. The configuration therefore is not
an ancestor of `.allFeatures`, whose cold-partial policy keeps them. -/
theorem completeCodeGlobal_not_in_join :
    (Tier.cfg .completeCodeGlobal).completeCodeWitness = true ∧
      (Tier.cfg .allFeatures).completeCodeWitness = false := ⟨rfl, rfl⟩

/-- Tiers are ordered by domain inclusion; this is a *declaration*, not a proved refinement. The
refinement obligations are W12's (`relSuccessor_*_mono`), and they need the adapter agreement
theorems below plus the still-missing semantic families.

**The earlier rank order was false.** Measured on the 3,138 nearcore-valid cases Lean refused, the
named tiers are not cumulative: `.curveHosts` and `.resharding` omit `globalActions`, so each
*excludes* 222 chunks its rank-8 predecessor decides; `.completeCodeGlobal` is narrower than
`.globalActions` (its complete-code policy rejects 76 valid warm-cache chunks), so it cannot be an
ancestor of any widest tier. `.allFeatures` is the first tier that actually composes every
implemented feature; only for it does "higher rank" mean "wider domain" among the wide tiers.
The rank remains a *declaration*: no refinement theorem is proved. -/
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

end NearSpecV3.Successor
