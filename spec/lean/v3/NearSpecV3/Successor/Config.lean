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

/-- The Wasm configuration of this protocol run. A function of `floats` and `loadingLimits`: the successor does not
admit an arbitrary `NearCfg` that could drift from the declared protocol version. -/
def ProtocolCfg.wasm (cfg : ProtocolCfg) : Wasm.NearCfg :=
  { (if cfg.floats then Wasm.floatPv86 else Wasm.pv86) with loadingLimits := cfg.loadingLimits }

/-- The signed configuration: exactly `checkD3`'s arguments. -/
def signedCfg : ProtocolCfg := {}

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
    if cfg.storageResolution then
      if cfg.genesisMainTransition then
        checkD2CoreGWith (recorderDriver cfg.wasm) (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
      else
        checkD2CoreWith (recorderDriver cfg.wasm) (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
    else if cfg.genesisMainTransition then
      checkD2CoreG (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
    else
      checkD2Core (D3.d3Hooks cfg.wasm) true claimBytes witnessBytes cfg.gasCap
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

/-- Tiers are ordered by domain inclusion; this is a *declaration*, not a proved refinement. The
refinement obligations are W12's (`relSuccessor_*_mono`), and they need the adapter agreement
theorems below plus the still-missing semantic families. -/
def Tier.rank : Tier → Nat
  | .signed => 0 | .floats => 1 | .protoGas => 2 | .floatsProtoGas => 3
  | .genesis => 4 | .genesisFloatsProtoGas => 5 | .runtimeLimits => 6 | .storageResolution => 7

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
