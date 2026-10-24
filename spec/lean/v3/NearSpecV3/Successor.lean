import NearSpecV3.Successor.Config
import NearSpecV3.Successor.HostDispatch
import NearSpecV3.Successor.ActionsReceipts
import NearSpecV3.Successor.Resolution
import NearSpecV3.Successor.TrieRecorder
import NearSpecV3.Successor.BoundaryFacts
import NearSpecV3.Successor.Differential

/-!
# W00 — the successor API

One root, seven interfaces. This module is the import point W02–W14 use; it re-exports the seven
interface modules and states the two facts that hold *across* them:

* **The signed statement is preserved.** `signedChecker_eq_checkD3` restates the tier module's
  definitional equality at the API's own name, so an importer cannot reach the successor without
  passing the signed entry point.
* **The signed statement's exclusions are named once.** `signedExclusions` lists every shape feature the
  signed checker refuses, with the successor owner who removes it. A lane that removes an exclusion must
  edit this list, which is the W00 owner map's Lean-side form.

## Interfaces and owners

| # | Module | Contract | Owner |
|---|---|---|---|
| 1 | `Successor/Config.lean` | canonical checker, explicit protocol configuration, tier predicates | L0 |
| 2 | `Successor/HostDispatch.lean` | additive host table; real-state/gas/error semantics; no host-result oracle | L0 |
| 3 | `Successor/ActionsReceipts.lean` | versioned actions/receipts, tags, dispatch, rollback, distribution receipts, key forms | L0 |
| 4 | `Successor/Resolution.lean` | local/global/ETH-wallet identifiers, code lookup, deploy tracking, defined cache | L0 |
| 5 | `Successor/TrieRecorder.lean` | read/write/remove/code access, per-receipt accounting, soft limit, rollback | L0 |
| 6 | `Successor/BoundaryFacts.lean` | genesis/epoch/layout/split inputs and authentication; external vs computed | L0 |
| 7 | `Successor/Differential.lean` | result/error vocabulary, expected domain, verdict, observables, no skipped match | L0 |

Each module's docstring records its own residual premises. This module adds none and removes none: it
only states the cross-interface facts and the owner map.

## What this module does not do

* It does not change `checkD3`, `RelD3`, `D2/Types.lean`, `D3/FunctionCall.lean`, `Wasm/Exec.lean`,
  `Wasm/Host.lean`, root imports or any signed schema. Every module is additive and lives under
  `NearSpecV3/Successor/`.
* It does not prove agreement with nearcore. Agreement is W13/W14's differential obligation; the
  differential vocabulary only makes a disagreement impossible to report as a match.
* It does not settle UQ-001, UQ-002, UQ-006, UQ-007, UQ-009, UQ-011, UQ-012 or UQ-015. Each is named at
  the interface that exposes it.
-/

namespace NearSpecV3.Successor

open NearSpec NearSpecV3

/-! ## The signed statement, preserved -/

/-- The signed tier is the signed checker: an importer of the successor API cannot bypass `checkD3`. -/
theorem signedChecker_eq_checkD3 (c w : Bytes) :
    Tier.checker .signed c w = D3.checkD3 c w := tier_signed_eq_checkD3 c w

/-- The signed tier's relation is the signed relation. -/
theorem signedRelation_iff_RelD3 (c w : Bytes) : Tier.rel .signed c w ↔ D3.RelD3 c w := Iff.rfl

/-- The signed checker's exclusion classification round-trips: an `out of domain` error is exactly an
exclusion, and a non-exclusion error is a rejection. -/
theorem signed_verdict_partition (c w : Bytes) :
    (checkVerdict D3.checkD3 c w).inDomain = true ∨
      ∃ r, checkVerdict D3.checkD3 c w = .outOfDomain r := by
  cases h : checkVerdict D3.checkD3 c w with
  | accept => exact Or.inl rfl
  | reject _ => exact Or.inl rfl
  | outOfDomain r => exact Or.inr ⟨r, rfl⟩

/-! ## The signed statement's exclusions and their owners

The signed checker refuses a set of shape features before running Wasm. Each is an exclusion (not a
reject) and each successor owner who removes it is named. This list is the Lean-side owner map; the
readable form with inventory row ids is `docs/research/lean-chunk-w00-owner-map.md`. -/

/-- A signed exclusion and the successor package that removes it. `none` = the exclusion stays in every
tier (it is a validator condition or a size bound, not a modelling gap). -/
structure SignedExclusion where
  /-- The feature name, matching `ShapeExclusion`. -/
  feature : ShapeExclusion
  /-- The successor package that removes it, or `none` if it stays excluded. -/
  owner : Option String
  deriving Repr

/-- Every signed exclusion, with its owner. `ShapeExclusion.removedBy` is the same mapping; this list
adds the ordering and the count. -/
def signedExclusions : List SignedExclusion :=
  [ ⟨.mlDsaKey, some "W05/W06"⟩
  , ⟨.mlDsaSignature, some "W05/W06"⟩
  , ⟨.deployGlobalContract, some "W07"⟩
  , ⟨.useGlobalContract, some "W07"⟩
  , ⟨.deterministicStateInit, some "W07"⟩
  , ⟨.globalContractDistribution, some "W07 (UQ-006)"⟩
  , ⟨.noCode, none⟩
  , ⟨.witnessSize, none⟩
  , ⟨.claimSize, none⟩
  , ⟨.resharding, some "W11"⟩ ]

theorem signedExclusions_length : signedExclusions.length = 10 := rfl

/-- Every exclusion's owner in the list is the mapping's owner. This is the consistency check that
keeps the owner map from drifting from the exclusion type. -/
theorem signedExclusions_owner_consistent (e : SignedExclusion) (h : e ∈ signedExclusions) :
    e.owner = e.feature.removedBy := by
  simp only [signedExclusions, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The exclusions that stay in every tier: the no-code requirement and the two size bounds. -/
def permanentExclusions : List ShapeExclusion :=
  signedExclusions.filterMap (fun e => if e.owner.isNone then some e.feature else none)

theorem permanentExclusions_length : permanentExclusions.length = 3 := rfl

/-- The three permanent exclusions are exactly no-code and the two size bounds. -/
theorem permanentExclusions_eq :
    permanentExclusions = [.noCode, .witnessSize, .claimSize] := rfl

/-! ## The exclusion count and the tier ladder

The signed tier excludes all ten features above. Each later tier removes the features its owner
package removes; **this API deliberately does not fix the tier → feature mapping**, because that is
W12's refinement obligation (`LEAN_CHUNK_COMPLETION_WORKPLAN.md`, W12). What this module does fix:

* the signed tier's exclusion set is exactly `signedExclusions` (ten features);
* three of those are permanent and stay in *every* tier (`permanentExclusions`);
* every exclusion's owner in the list is `ShapeExclusion.removedBy`'s owner
  (`signedExclusions_owner_consistent`).

No theorem here proves the tiers are nested by inclusion, and no count is claimed for the later
tiers. A lane that removes an exclusion updates `signedExclusions` (and therefore
`permanentExclusions`) and its own module's tier predicate; it does not edit `checkD3`. -/

/-- **The list is complete and duplicate-free.** The exclusion list's features are exactly the ten
`ShapeExclusion` constructors, in declaration order: no exclusion is missing and none is listed twice.
This is the check that keeps the owner map from silently dropping or double-counting a row. -/
theorem signedExclusions_features :
    signedExclusions.map (·.feature) =
      [.mlDsaKey, .mlDsaSignature, .deployGlobalContract, .useGlobalContract,
       .deterministicStateInit, .globalContractDistribution, .noCode, .witnessSize,
       .claimSize, .resharding] := rfl

/-- Every `ShapeExclusion` appears in the owner list exactly once. -/
theorem signedExclusions_covers (f : ShapeExclusion) :
    (signedExclusions.filter (fun e => e.feature == f)).length = 1 := by
  cases f <;> rfl

/-! ## Axiom-closure check points -/

#print axioms signedChecker_eq_checkD3
#print axioms signedExclusions_owner_consistent
#print axioms permanentExclusions_eq
#print axioms signedExclusions_covers

end NearSpecV3.Successor
