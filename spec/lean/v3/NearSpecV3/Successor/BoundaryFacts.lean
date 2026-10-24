import NearSpecV3.ClaimV3
import NearSpecV3.ReshardingD3

/-!
# W00 interface 6/7 — boundary facts and their authentication obligations

The successor statement takes more than the signed D2 claim: genesis extra, epoch validators, split
gates, the minimum stake, tx-validity facts and the computed outputs all enter a chunk's verdict.
W12 owns genesis injection, W13 owns witness capture and W11 owns resharding/mixed-epoch semantics;
each needs one agreed vocabulary for *what a boundary fact is and where its authentication lives*.

## The vocabulary

* `BoundaryFact` — an inductive of the facts a successor statement admits. Each constructor's docstring
  names the claim-v3 field or the external input it comes from. The list is closed: a new fact is a
  source change reviewed with the interface, not a silent `String`.
* `FactKind` — `external` (admitted from outside the statement, needs authentication) or `computed`
  (an output the statement must *produce*, needs a check but no admission).
* `BoundaryFact.obligation` — the claim-v3 T-number / admission contract each fact's authentication
  lives in. This is a *name*, so a lane cannot quietly drop the obligation without dropping the fact.
* `BoundaryInputs` — the successor's admitted inputs, grouped by where they come from: genesis, epoch,
  split, and the remaining external facts. `ofClaim` projects the facts that are already in the claim.
* `FactAuthentication` — the contract an external fact must satisfy before the statement admits it: the
  fact's value is *fixed by the witness or the claim* and its obligation id is non-empty. `Authenticated`
  is the structure-form statement, so "authenticated" is not a runtime flag.

## What is not established

* **No fact is authenticated here.** `FactAuthentication` is a contract; W12/W13 must supply instances.
  In particular the genesis `genesisChunkExtra`/`genesisBlockHash` admission is UQ-007's obligation and
  is not discharged by naming it.
* **`obligation` is documentation with a type.** The mapping is asserted to be total and non-empty
  (`obligation_nonempty`); it is not proved to match claim-v3's text. That cross-check is W13's.
* **The computed facts are not computed.** `stateRoot`, `outcomeRoot`, `gasUsed`, `balanceBurnt`,
  `outgoingReceiptsRoot`, `congestionInfo`, `bandwidthRequests` and `validatorProposals` are named as
  outputs; W13/W14 own producing and comparing them. The differential module compares *observables*,
  not these facts.
* **The mixed-epoch / split facts do not change the signed statement.** `SplitInputs` carries the split
  gate; `ReshardingD3`'s `noResharding` already excludes resharded claims from D3α. W11 owns the
  successor semantics for claims that *do* cross a boundary; this module only names the input.
-/

namespace NearSpecV3.Successor

open NearSpec NearSpecV3 NearSpecV3.D3

/-! ## The facts -/

/-- Every boundary fact a successor statement admits. The `external` block is admitted from outside the
statement (claim field or witness input); the `computed` block is an output the statement must produce. -/
inductive BoundaryFact where
  /-- `c.chainId` — the chain the chunk belongs to. -/
  | chainId
  /-- Epoch validators from the epoch table / genesis. -/
  | epochValidators
  /-- `minimum_stake` from the protocol parameters. -/
  | minimumStake
  /-- Tx-validity facts of the chunk's transactions. -/
  | txValid
  /-- Runtime-config resharding parameters. -/
  | rsParams
  /-- A validator update carried by the chunk's block. -/
  | validatorUpdate
  /-- The split gate (resharding boundary) of the chunk's epoch. -/
  | splitGate
  /-- The genesis chunk extra (main transition), UQ-007. -/
  | genesisChunkExtra
  /-- The genesis block hash, UQ-007. -/
  | genesisBlockHash
  /-- The post-state root: an output. -/
  | stateRoot
  /-- The outcome root: an output. -/
  | outcomeRoot
  /-- Gas burnt: an output. -/
  | gasUsed
  /-- Balance burnt: an output. -/
  | balanceBurnt
  /-- Outgoing receipts root: an output. -/
  | outgoingReceiptsRoot
  /-- Congestion info per shard: an output. -/
  | congestionInfo
  /-- Bandwidth requests: an output. -/
  | bandwidthRequests
  /-- Validator proposals: an output. -/
  | validatorProposals
  deriving DecidableEq, Repr

/-- Where a fact comes from. -/
inductive FactKind where
  | external
  | computed
  deriving DecidableEq, Repr

/-- The kind of each fact. -/
def BoundaryFact.kind : BoundaryFact → FactKind
  | .chainId | .epochValidators | .minimumStake | .txValid | .rsParams
  | .validatorUpdate | .splitGate | .genesisChunkExtra | .genesisBlockHash => .external
  | .stateRoot | .outcomeRoot | .gasUsed | .balanceBurnt | .outgoingReceiptsRoot
  | .congestionInfo | .bandwidthRequests | .validatorProposals => .computed

/-- The claim-v3 obligation each fact's authentication lives in. A name per fact, so dropping the
obligation means dropping the fact. -/
def BoundaryFact.obligation : BoundaryFact → String
  | .chainId => "T3 (c.chainId)"
  | .epochValidators => "T4 (c.epochs[].validators)"
  | .minimumStake => "T4 (protocol parameters)"
  | .txValid => "T7 (c.transactions[] validity)"
  | .rsParams => "T4 (resharding parameters)"
  | .validatorUpdate => "T4 (c.validatorUpdate)"
  | .splitGate => "T4 (c.splitGate)"
  | .genesisChunkExtra => "UQ-007 (genesis extra; owner L6)"
  | .genesisBlockHash => "UQ-007 (genesis block hash; owner L6)"
  | .stateRoot => "computed output"
  | .outcomeRoot => "computed output"
  | .gasUsed => "computed output"
  | .balanceBurnt => "computed output"
  | .outgoingReceiptsRoot => "computed output"
  | .congestionInfo => "computed output"
  | .bandwidthRequests => "computed output"
  | .validatorProposals => "computed output"

theorem obligation_nonempty (f : BoundaryFact) : (f.obligation).length > 0 := by
  cases f <;> decide

theorem genesisChunkExtra_external : BoundaryFact.genesisChunkExtra.kind = .external := rfl
theorem stateRoot_computed : BoundaryFact.stateRoot.kind = .computed := rfl

/-! ## The admitted inputs -/

/-- Genesis facts a successor statement admits. Both are optional: a non-genesis chunk carries neither,
and a genesis chunk carries them in its witness (`chunk_validation.rs:248-258`). -/
structure GenesisInputs where
  /-- The genesis chunk extra, when this chunk is a genesis chunk's main transition. -/
  genesisChunkExtra : Option Bytes := none
  /-- The genesis block hash, when this chunk is a genesis chunk's main transition. -/
  genesisBlockHash : Option Bytes := none
  deriving DecidableEq, Repr

/-- Epoch facts a successor statement admits. The epoch table and the first epoch after the chunk,
plus the shard layouts for mixed-epoch claims. -/
structure EpochInputs where
  epochs : List EpochRec := []
  epochStartAfter : Bytes := []
  /-- The distinct shard layouts of the claim's epochs, in order (`EpochRec.shardLayout`). -/
  layouts : List Bytes := []
  deriving Repr

/-- The distinct shard layouts of an epoch table, in first-occurrence order. -/
def EpochInputs.layoutsOf (es : List EpochRec) : List Bytes :=
  (es.map (fun e => e.shardLayout)).foldl
    (fun acc l => if acc.contains l then acc else acc ++ [l]) []

theorem layoutsOf_nil : EpochInputs.layoutsOf [] = [] := rfl

/-- The split gates the claim carries, in order (`c.applyFacts[].splitGate`); the signed
`c.no_split_gate` already requires every one to be `none` on a D3α claim. -/
def splitGatesOf (c : Claim) : List SplitGate :=
  c.applyFacts.filterMap (fun f => f.splitGate)

/-- The split gate's facts: whether the chunk's epoch crosses a resharding boundary and, if so, the
child shard layouts. `none` means "no split gate supplied", which the signed `c.no_split_gate` already
requires to be absent. -/
structure SplitInputs where
  /-- The claim's first split gate, if any (`c.applyFacts[].splitGate`). -/
  splitGate : Option SplitGate := none
  /-- The child shard layouts a split produces (W11's input; empty for the signed statement). -/
  childShards : List Bytes := []
  deriving Repr

/-- The successor's admitted boundary inputs. The claim-derived facts are separate from the witness
inputs, so `ofClaim` is a projection and not a guess. -/
structure BoundaryInputs where
  /-- Facts already present in the claim (`c.chainId`, epochs, split gate). -/
  chainId : Bytes := []
  epochs : EpochInputs := {}
  split : SplitInputs := {}
  /-- Facts only the witness carries. -/
  genesis : GenesisInputs := {}
  deriving Repr

theorem splitGatesOf_nil : splitGatesOf ⟨86, [], [], [], [], 0, 0, [], [], [], [], none⟩ = [] := rfl

/-- Project the boundary inputs the claim already carries. The genesis facts are *not* taken from the
claim: they are witness inputs (`none` here), so `ofClaim` cannot smuggle them in. -/
def BoundaryInputs.ofClaim (c : Claim) : BoundaryInputs where
  chainId := c.chainId
  epochs := { epochs := c.epochs, epochStartAfter := c.epochStartAfter
              layouts := EpochInputs.layoutsOf c.epochs }
  split := { splitGate := (splitGatesOf c).head?, childShards := [] }
  genesis := {}

theorem ofClaim_chainId (c : Claim) : (BoundaryInputs.ofClaim c).chainId = c.chainId := rfl
theorem ofClaim_no_genesis (c : Claim) : (BoundaryInputs.ofClaim c).genesis.genesisChunkExtra = none := rfl
theorem ofClaim_epochs (c : Claim) : (BoundaryInputs.ofClaim c).epochs.epochs = c.epochs := rfl

/-- The claim's genesis extra is *not* lifted into the boundary inputs; it stays a witness input. -/
theorem ofClaim_genesis_extra_absent (c : Claim) :
    (BoundaryInputs.ofClaim c).genesis.genesisChunkExtra = none ∧
      c.genesisChunkExtra = c.genesisChunkExtra := ⟨rfl, rfl⟩

/-! ## Authentication contract -/

/-- A fact is *authenticated* when its value is fixed by the claim or the witness and its obligation id
is non-empty. The `fixedBy` field names the claim field or witness key; the obligation is the T-number.
This is a structure, so "authenticated" is a supplied proof, never a runtime flag. -/
structure FactAuthentication where
  fact : BoundaryFact
  /-- The claim field or witness key that fixes the value. -/
  fixedBy : String
  /-- The claim-v3 obligation the admission lives in. -/
  obligation : String
  /-- The obligation id is the fact's own obligation (no dangling names). -/
  obligation_eq : obligation = fact.obligation
  /-- The value is fixed, not free: a name is always present. -/
  fixedBy_nonempty : fixedBy.length > 0

theorem authObligation_is_fact_obligation (a : FactAuthentication) :
    a.obligation = a.fact.obligation := a.obligation_eq

/-- An external fact's authentication must be supplied before the statement admits it. -/
def FactAuthentication.isExternal (a : FactAuthentication) : Bool :=
  a.fact.kind = .external

theorem genesisChunkExtra_requires_auth (a : FactAuthentication)
    (h : a.fact = .genesisChunkExtra) : a.isExternal = true := by
  rw [FactAuthentication.isExternal, h, genesisChunkExtra_external]
  rfl

/-! ## The signed statement's exclusions, as boundary facts

The signed D3α checker excludes shape features *before* running a single Wasm instruction. Those
exclusions are not facts to admit; they are the boundary of the statement. Restating them here keeps the
successor's "out of domain" and "reject" split honest: an exclusion is never an authentication failure. -/

/-- The shape features the signed checker excludes (`D2/Types.lean`'s `isShapeOOD` list and D2's
`out of domain (w.*)`/`c.*` checks). Each is an *exclusion*, so a successor tier that admits it must say
so explicitly. -/
inductive ShapeExclusion where
  | mlDsaKey
  | mlDsaSignature
  | deployGlobalContract
  | useGlobalContract
  | deterministicStateInit
  | globalContractDistribution
  | noCode
  | witnessSize
  | claimSize
  | resharding
  deriving DecidableEq, Repr

/-- The message prefix each signed exclusion produces. The successor's `isExclusion` test reads this
prefix, so an exclusion is recognised by its own text and not by a hand-maintained list. -/
def ShapeExclusion.prefix : ShapeExclusion → String
  | .mlDsaKey => "out of domain (w.shape)"
  | .mlDsaSignature => "out of domain (w.shape)"
  | .deployGlobalContract => "out of domain (w.shape)"
  | .useGlobalContract => "out of domain (w.shape)"
  | .deterministicStateInit => "out of domain (w.shape)"
  | .globalContractDistribution => "out of domain (w.shape)"
  | .noCode => "out of domain (w.no_code)"
  | .witnessSize => "out of domain (w.size)"
  | .claimSize => "out of domain (c.size)"
  | .resharding => "out of domain (c.resharding)"

theorem resharding_prefix : ShapeExclusion.resharding.prefix = "out of domain (c.resharding)" := rfl

/-- The successor tier that removes an exclusion. `none` = still excluded (the signed tier). -/
def ShapeExclusion.removedBy : ShapeExclusion → Option String
  | .mlDsaKey => some "W05/W06"
  | .mlDsaSignature => some "W05/W06"
  | .deployGlobalContract => some "W07"
  | .useGlobalContract => some "W07"
  | .deterministicStateInit => some "W07"
  | .globalContractDistribution => some "W07 (UQ-006)"
  | .noCode => none
  | .witnessSize => none
  | .claimSize => none
  | .resharding => some "W11"

theorem noCode_not_removed : ShapeExclusion.noCode.removedBy = none := rfl
theorem resharding_removed_by_w11 : ShapeExclusion.resharding.removedBy = some "W11" := rfl

/-! ## Axiom-closure check points -/

#print axioms obligation_nonempty
#print axioms genesisChunkExtra_requires_auth

end NearSpecV3.Successor
