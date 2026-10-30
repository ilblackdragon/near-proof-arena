import NearSpecV3.Successor.ReshardCore

/-!
# `D3.checkD3` / `D3.RelD3` — the signed statement of record

`checkD3` is the statement of record (`docs/research/lean-chunk-w00-owner-map.md` §3.1). Up to
2026-10-28 it was `checkD2Core (d3Hooks Wasm.pv86) true … (some gAlpha)`, which is now
`D3.checkD3Core` (`D3/FunctionCall.lean`). That legacy pipeline has two stated preconditions under
which it is not a model of the validator, and it reported every valid chunk outside them as excluded
or — worse — rejected:

1. **One shard layout, no split check.** It reads the whole segment in one layout and has no split
   semantics:
   * `out of domain (c.same_layout): resharding` — the claim's epochs carry different shard layouts
     (a child's first chunks after a split, and the parent's chunks in the epoch before);
   * `out of domain (c.same_layout): outgoing buffer to a shard outside the layout` — the shard still
     has buffered receipts addressed to a split parent (`forward_from_buffer`,
     `runtime/runtime/src/congestion_control.rs:236-286`, forwards them to the parent's children);
   * `out of domain (c.no_split_gate)` — the applied block runs the dynamic-resharding split check
     (pre-split gating: the header's `proposed_split` is recomputed from the trie,
     `check_dynamic_resharding` / `find_trie_split`).
2. **The storage-proof limits never trigger.** It reveals the whole recorded trie and runs every
   receipt, which is nearcore's behaviour only while `main_storage_proof_size_soft_limit` and
   `per_receipt_storage_proof_size_limit` (4,000,000 B each at PV86) are not reached. It asserts this
   with the conservative `w.size` bound `Σ|values ++ codes| + 2000·removals ≤ 4,000,000`
   (`out of domain (w.size): storage-proof upper bound …`), checked *after* the main transition. On
   a witness above the bound nearcore postpones receipts, so the witness legitimately lacks values the
   legacy pipeline reads: it then rejected valid chunks with `MissingTrieValue` before reaching its
   own bound (the 26 nearcore-valid `storage-limit-fixtures` cases). A contract-code-heavy chunk is
   excluded by the same bound, because code blobs are counted in it.

**UQ-010 decision (user, 2026-10-27): a signed-tier exclusion or reject of a valid chunk is fixed as
a strengthening of the signed statement.** `checkD3` keeps the legacy core and, *only* outside its
preconditions, decides with the recorder engine the successor already validates against nearcore
(`Successor.ReshardCore` / `StorageExecution`; `docs/evidence/lean-chunk-completion/
resharding-fixtures{,-2}/`, `storage-limit-fixtures/`) at the signed feature set
(`signedReshardDriver`): the same `Wasm.pv86` configuration and `G_α` cap, the clear
`near-arena-witness-v3` format, the 8 MiB state-witness bound, `c.segment` and `c.layout`; no global
actions, curve hosts or floats. The recorder models both storage-proof limits exactly, so the
conservative merged-value bound is not applied there; nearcore's 64 MiB `ContractCodeResponse` cap
is (`w.code_response_size`). A segment that reaches genesis is handed to the one-layout recorder
pipeline (`checkD2CoreWith`), which keeps `c.same_layout` (`LayoutReach.genesis_segment_one_layout`:
no honest genesis segment has a layout change).

The hand-over fires (`handover`) exactly when the legacy result is an error and
* it is one of the resharding exclusions (precondition 1), or
* it is the storage-proof `w.size` exclusion, or the witness's values and code exceed 4,000,000 bytes
  (precondition 2). On such a witness the legacy core can never accept (its `w.size` check is
  necessary for acceptance), so its error is a premature exclusion.

What this changes, as proved below:

* `checkD3_of_core_ok`: every claim the legacy core accepted is still accepted, with no change.
* `checkD3_cases`: `checkD3` returns exactly the legacy result, unless the legacy result was an error
  on which `handover` fires.
-/

namespace NearSpecV3.Successor

open NearSpec NearSpecV3

/-- Byte-list prefix test (as `Config.isExclusion`), so that no `String.startsWith` lemma enters
the relation. -/
def hasPrefixL (p : List Char) (e : String) : Bool := e.toList.take p.length == p

/-- The legacy-pipeline exclusions that come from its one-layout precondition. -/
def reshardHandoverPrefixes : List (List Char) :=
  ["out of domain (c.same_layout)".toList, "out of domain (c.no_split_gate)".toList]

/-- Whether a legacy error is one of the resharding exclusions. -/
def reshardHandover (e : String) : Bool := reshardHandoverPrefixes.any fun p => hasPrefixL p e

/-- The legacy pipeline's storage-proof exclusion (its conservative `w.size` bound). -/
def storageProofPrefix : List Char := "out of domain (w.size): storage-proof".toList

/-- `Σ |values| + Σ |codes|` of the main transition, the base of the legacy `w.size` bound
(`checkD2CoreObs`: `baseBytes` of `w.main.values ++ codes`); `0` when the witness does not decode
(the legacy result is then the decoder's own error, and stays). -/
def legacyMergedBytes (witnessBytes : Bytes) : Nat :=
  match decodeWitnessFile witnessBytes with
  | .ok (sw, codes) => match decodeStateWitnessD2 sw with
    | .ok w => ((w.main.values ++ codes).map List.length).foldl (· + ·) 0
    | .error _ => 0
  | .error _ => 0

/-- The legacy core's storage-proof bound (`legacyDriver.sizeOk` with no removals). -/
def legacyStorageBound : Nat := 4000000

/-- When the signed statement decides a legacy error with the recorder engine (module comment). -/
def handover (e : String) (witnessBytes : Bytes) : Bool :=
  reshardHandover e || hasPrefixL storageProofPrefix e ||
    decide (legacyStorageBound < legacyMergedBytes witnessBytes)

/-- The recorder engine at the signed feature set, deciding resharding. Exact storage-proof limits
(the recorder's `sizeOk` is `true`), nearcore's code-response cap, and the clear witness format; the
8 MiB state-witness bound, `c.segment` and `c.layout` stay because the driver's lift flags keep their
`false` defaults. -/
def signedReshardDriver (cfg : Wasm.NearCfg) : ExecutionDriver :=
  { reshardingDriver cfg false .coldPartial with compressedWitness := false }

/-- The same, one shard layout (for a segment that reaches genesis). -/
def signedRecorderDriver (cfg : Wasm.NearCfg) : ExecutionDriver :=
  { recorderDriver cfg false .coldPartial with compressedWitness := false }

/-- The recorder-engine decision of the signed statement. -/
def signedRecorderCheck (cfg : Wasm.NearCfg) (gasCap : Option Nat) (claimBytes witnessBytes : Bytes) :
    Except String Unit :=
  if segmentHasGenesis claimBytes then
    checkD2CoreWith (signedRecorderDriver cfg) (D3.d3Hooks cfg) true claimBytes witnessBytes gasCap
  else
    checkReshardCore (signedReshardDriver cfg) (D3.d3Hooks cfg) true claimBytes witnessBytes gasCap

/-- Keep a legacy result, unless it is an error on which `handover` fires; then decide with the
recorder engine. -/
def withReshardHandover (cfg : Wasm.NearCfg) (gasCap : Option Nat) (r : Except String Unit)
    (claimBytes witnessBytes : Bytes) : Except String Unit :=
  match r with
  | .ok u => .ok u
  | .error e =>
    if handover e witnessBytes then signedRecorderCheck cfg gasCap claimBytes witnessBytes
    else .error e

theorem withReshardHandover_ok (cfg : Wasm.NearCfg) (gasCap : Option Nat) (c w : Bytes) :
    withReshardHandover cfg gasCap (.ok ()) c w = .ok () := rfl

/-- The hand-over returns the legacy result, unless that result is an error on which `handover`
fires. -/
theorem withReshardHandover_cases (cfg : Wasm.NearCfg) (gasCap : Option Nat)
    (r : Except String Unit) (c w : Bytes) :
    withReshardHandover cfg gasCap r c w = r ∨
      ∃ e, r = .error e ∧ handover e w = true ∧
        withReshardHandover cfg gasCap r c w = signedRecorderCheck cfg gasCap c w := by
  cases r with
  | ok u => exact .inl rfl
  | error e =>
    cases hc : handover e w
    · exact .inl (by simp only [withReshardHandover, hc, Bool.false_eq_true, ite_false])
    · exact .inr ⟨e, rfl, hc, by simp only [withReshardHandover, hc, ite_true]⟩

end NearSpecV3.Successor

namespace NearSpecV3.D3

open NearSpecV3 NearSpecV3.Successor

/-- **`Rel_D3` checker, the signed statement of record.** `checkD3Core` (the D2 pipeline with WASM
execution behind the FunctionCall hook, `D3/FunctionCall.lean`), decided by the recorder engine at the
signed feature set outside the core's two preconditions (module comment). `InD3α` is `InD2` minus
`e.wasm`/`w.no_code`, minus resharding and minus the storage-proof bound, plus the WASM-level
conditions reported by the hook (`out of domain (e.wasm-α) …`) and the per-chunk cap
`out of domain (e.g_alpha)`.

**Cache independence.** `Rel_D3` is the cold-cache statement: the code of every executed pre-state
contract must be in the witness (`spec/near-chunk-validation-d3.md` §2.2). -/
def checkD3 (claimBytes witnessBytes : NearSpec.Bytes) : Except String Unit :=
  withReshardHandover Wasm.pv86 (some gAlpha) (checkD3Core claimBytes witnessBytes)
    claimBytes witnessBytes

def RelD3 (claimBytes witnessBytes : NearSpec.Bytes) : Prop := checkD3 claimBytes witnessBytes = .ok ()

/-- Every claim the legacy core accepts, `checkD3` accepts. -/
theorem checkD3_of_core_ok (c w : NearSpec.Bytes) (h : checkD3Core c w = .ok ()) :
    checkD3 c w = .ok () := by
  unfold checkD3; rw [h]; rfl

/-- `checkD3` is the legacy core, except on the core's errors outside its preconditions. -/
theorem checkD3_cases (c w : NearSpec.Bytes) :
    checkD3 c w = checkD3Core c w ∨
      ∃ e, checkD3Core c w = .error e ∧ handover e w = true ∧
        checkD3 c w = signedRecorderCheck Wasm.pv86 (some gAlpha) c w :=
  withReshardHandover_cases Wasm.pv86 (some gAlpha) (checkD3Core c w) c w

/-- **The D3 relation as a decidable boolean.**  A `Bool` mirror of the `Except` checker, so the
kernel can evaluate the relation on concrete bytes, plus a `Decidable` instance.

Note the polarity differs from `RelD0`/`RelD1`/`RelD2` on purpose: those are *Bool-primary*
(`RelDk c w := acceptsDk c w = true`), while `RelD3` keeps the `Except` equation as its definition.
`relD3_iff_acceptsD3` proves the two agree, so this is a bridge, not a redefinition. -/
def acceptsD3 (claimBytes witnessBytes : NearSpec.Bytes) : Bool :=
  match checkD3 claimBytes witnessBytes with
  | .ok () => true
  | .error _ => false

theorem relD3_iff_acceptsD3 (c w : NearSpec.Bytes) : RelD3 c w ↔ acceptsD3 c w = true := by
  unfold RelD3 acceptsD3
  cases h : checkD3 c w with
  | ok u => cases u; simp
  | error e => simp

instance (c w : NearSpec.Bytes) : Decidable (RelD3 c w) :=
  decidable_of_iff (acceptsD3 c w = true) (relD3_iff_acceptsD3 c w).symm

#print axioms checkD3_of_core_ok
#print axioms checkD3_cases
#print axioms relD3_iff_acceptsD3

end NearSpecV3.D3
