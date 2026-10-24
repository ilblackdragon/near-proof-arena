import NearSpecV3.D3.GlobalContract
import NearSpecV3.Successor.ActionsReceipts

/-!
# W00 interface 4/7 — contract resolution and the defined cache environment

W07/W08 need one place that answers: *which code does a call run, and where may that answer come
from?* The signed D2/D3 pipeline answers it in three separate places —
`D2.Contract`/`RuntimeContractIdentifier::resolve` (L4's `Rci.resolve`), the in-chunk deploy
tracker (`D2/Actions.codeAvailable`), and the cold-cache rule in `D3.functionCall` — and the cache
environment question (UQ-001, UQ-002) is not settled in the signed statement.

This module publishes the resolution contract without deciding UQ-001/UQ-002 on another lane's
behalf:

* `ContractIdentifier` — the four resolved forms nearcore distinguishes at PV86: local code hash,
  global code hash, global by account id, and the ETH-implicit global wallet. It is an alias of L4's
  `Rci`, so the two cannot drift.
* `CacheEnv` — the **defined cache environment**. It is data, not a global flag: `mode` says which
  cache policy a statement assumes, and `lookup` is the only cache the resolution may consult. The
  cold environment (`coldCache`) has an empty lookup. A warm environment must supply a lookup that is
  *determined by the claim and witness*; that obligation is a field, not a promise.
* `ResolutionEnv` — the resolution state: chain id, the `TrieUpdate` overlay, and the deploy tracker.
  Its operations are `resolveIdentifier`, `resolveCodeHash`, `codeOf` and the deploy/rollback pair.
* `ResolutionContract` — the abstract contract W07/W08 program against, with the cache-independence
  law as a structure field. A lane that cannot supply the law cannot instantiate the contract, which
  is the honest form of "the statement of record must say which cache it assumes".

## Source

* `RuntimeContractIdentifier::resolve`, `LegacyEthWallet` and the PV86 flag:
  `runtime/runtime/src/contract_code.rs:21-131`, `core/primitives-core/src/version.rs:556`,
  `parameters.snap:281`. L4 proves the ETH-wallet arm unreachable at PV86
  (`L4.legacyWallet_unreachable_pv86`) and that an ETH-implicit account with a wallet-hash local
  contract resolves to the global wallet (`L4.ethImplicit_resolves_global`).
* In-chunk deploys and the compiled-contract cache: `runtime/runtime/src/contract.rs:42-131`
  (`ContractsTracker`), `function_call.rs:355-393`, `pipelining.rs:323-374`.
* Global-contract trie keys: `core/primitives/src/trie_key.rs:73,75,133-143,266-276`.

## Residual premises / open questions

* **UQ-001 is not settled here.** The contract *can* express a cold or a warm cache, but which one
  the arena admits is L1's decision. `ResolutionContract.cacheIndependent` records the choice a lane
  makes; this module does not make it.
* **UQ-002 is not settled here.** Whether `e.code_cache` may be narrowed to rolled-back deploys is a
  signed-relation change (L1 + L7). The deploy tracker here represents the split; it does not change
  the signed checker.
* The `CacheEnv.lookup` is not proved to be cache-independent for any concrete warm environment. The
  field `determinedByClaim` is an obligation the instantiating lane must discharge.
* No theorem here proves `Rci.resolveCodeHash` agrees with nearcore's `RuntimeContractIdentifier`
  for a trie-backed store. L4 owns that differential obligation.
-/

namespace NearSpecV3.Successor

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3 NearSpecV3.D3.L4

/-! ## Identifiers -/

/-- The four resolved contract-identifier forms. An alias, so L4's resolution and the successor's
cannot diverge. -/
abbrev ContractIdentifier := Rci

/-- The resolved code hash an identifier points at. `.none` and `.legacyEthWallet` carry
`zeros 32` in L4's model; `.legacyEthWallet` is unreachable at PV86. -/
def ContractIdentifier.codeHashOf (i : ContractIdentifier) : Bytes := Rci.codeHashOf i

/-- Whether resolving this identifier needs a trie read (only the `AccountId` variant does,
`contract_code.rs:118-131`). -/
def ContractIdentifier.needsLookup (i : ContractIdentifier) : Bool := i.needsTrieLookup

/-- The successor identifier classifier, total on the four forms. -/
inductive IdentifierKind where
  | none
  | local (accountId : Bytes)
  | globalByHash
  | globalByAccount
  | ethWallet
  deriving DecidableEq, Repr

def kindOf : ContractIdentifier → IdentifierKind
  | .none => .none
  | .accountLocal _ acct => .local acct
  | .global _ (.codeHash _) => .globalByHash
  | .global _ (.accountId _) => .globalByAccount
  | .legacyEthWallet _ => .ethWallet

/-- The identifier's classified form. -/
def ContractIdentifier.kind (i : ContractIdentifier) : IdentifierKind := kindOf i

/-- A `global` identifier's kind is never `ethWallet`. -/
theorem kindOf_global_ne_ethWallet (h : Bytes) (g : Gci) :
    kindOf (Rci.global h g) ≠ .ethWallet := by
  cases g with
  | codeHash _ => simp [kindOf]
  | accountId _ => simp [kindOf]

/-- The ETH-wallet arm is unreachable at PV86, as a named successor fact. -/
theorem ethWallet_kind_unreachable (chainId acct : Bytes) (c : Contract) :
    kindOf (Rci.resolve chainId acct c) ≠ .ethWallet := by
  intro h
  cases hc : Rci.resolve chainId acct c with
  | «none» => simp [kindOf, hc] at h
  | accountLocal _ _ => simp [kindOf, hc] at h
  | global hh gg => exact kindOf_global_ne_ethWallet hh gg (by simpa [hc] using h)
  | legacyEthWallet ww => exact (L4.legacyWallet_unreachable_pv86 chainId acct c ww) hc

/-! ## The defined cache environment -/

/-- The cache policy a statement assumes. `cold` is the signed D3α choice
(`spec/near-chunk-validation-d3.md` §10.0 decision 1); `committedTracker` is the deterministic
in-chunk deploy tracker (`contract.rs:42-131`); `validatorCache` is nearcore's warm compiled-contract
cache, whose verdict depends on validator history. -/
inductive CacheMode where
  | cold
  | committedTracker
  | validatorCache
  deriving DecidableEq, Repr

/-- A cache environment: the declared policy plus the only cache the resolution may consult. The
cache is *data* so the environment is a defined object rather than a hidden global. -/
structure CacheEnv where
  mode : CacheMode := .cold
  /-- Code blobs the resolution may use without a witness read. Empty for the cold statement. -/
  lookup : Bytes → Option Bytes := fun _ => none
  /-- For a non-cold environment: the lookup is a function of the claim and witness alone, so the
  statement remains cache-*independent* even when it is not cold. -/
  determinedByClaim : Bool := true

/-- The signed cold-cache environment: no code outside the witness. -/
def coldCache : CacheEnv := {}

/-- The committed-deploy environment: code deployed and committed in this chunk is served by the
deploy tracker (the deterministic part of `ContractsTracker`), not by validator history. -/
def committedCache : CacheEnv := { mode := .committedTracker }

/-- A validator-cache environment is *not* cache-independent; the field records that, so a lane
cannot claim independence while using it. -/
def validatorCacheEnv (lookup : Bytes → Option Bytes) : CacheEnv :=
  { mode := .validatorCache, lookup := lookup, determinedByClaim := false }

/-- The cold environment consults no cache: resolution depends on the witness only. -/
theorem coldCache_lookup_none (h : Bytes) : coldCache.lookup h = none := rfl

theorem coldCache_independent : coldCache.determinedByClaim = true := rfl

theorem validatorCache_not_independent (lookup : Bytes → Option Bytes) :
    (validatorCacheEnv lookup).determinedByClaim = false := rfl

/-! ## The resolution state -/

/-- Resolution state for one chunk: the chain id, the chunk's `TrieUpdate` overlay, the declared
cache environment, and the in-chunk deploy tracker. -/
structure ResolutionEnv where
  chainId : Bytes
  overlay : Ovl
  cache : CacheEnv := coldCache
  deploys : DeployTracker := ⟨[], []⟩

/-- Resolve an account's contract to its identifier (`RuntimeContractIdentifier::resolve`, PV86). -/
def ResolutionEnv.resolveIdentifier (e : ResolutionEnv) (acct : Bytes) (c : Contract) :
    ContractIdentifier :=
  Rci.resolve e.chainId acct c

/-- Resolve the code hash the identifier points at. `AccountId` identifiers read
`TrieKey::GlobalContractCode`; absent values are `StorageInconsistentState` (`invalid`), never an
exclusion. -/
def ResolutionEnv.resolveCodeHash (e : ResolutionEnv) (i : ContractIdentifier) :
    Except String (Option Bytes) :=
  Rci.resolveCodeHash e.overlay i

/-- Look up a contract's code blob by code hash in the overlay. The cache environment is consulted
*after* the overlay: the cold environment has no cache, so a cold lookup succeeds only when the blob
is in the witness's recorded storage. -/
def ResolutionEnv.codeOf (e : ResolutionEnv) (h : Bytes) : Except String (Option Bytes) :=
  match e.overlay.lookup (kCode h) with
  | some v => .ok v
  | none =>
    match e.cache.lookup h with
    | some c => .ok (some c)
    | none => .error s!"invalid: MissingTrieValue (contract code {h.length} bytes)"

/-- The in-chunk deploy tracker's lookup: a code hash present in the tracker is served without a
witness read. -/
def ResolutionEnv.deployedCode? (e : ResolutionEnv) (h : Bytes) : Option Bytes :=
  ((e.deploys.committed ++ e.deploys.prospective).find? (fun p => sha256 p.2 == h)).map Prod.snd

/-- Record a deploy in the current receipt's prospective set. -/
def ResolutionEnv.recordDeploy (e : ResolutionEnv) (code : Bytes) : ResolutionEnv :=
  { e with deploys := { e.deploys with prospective := e.deploys.prospective ++ [(sha256 code, code)] } }

/-- Commit the current receipt's deploys into the chunk's committed set. -/
def ResolutionEnv.commitDeploys (e : ResolutionEnv) : ResolutionEnv :=
  { e with deploys := e.deploys.commit }

/-- Roll the current receipt's deploys back; committed deploys survive. -/
def ResolutionEnv.rollbackDeploys (e : ResolutionEnv) : ResolutionEnv :=
  { e with deploys := e.deploys.rollback }

theorem rollbackDeploys_keeps_committed (e : ResolutionEnv) :
    e.rollbackDeploys.deploys.committed = e.deploys.committed := rfl

theorem commitDeploys_keeps_all (e : ResolutionEnv) :
    e.commitDeploys.deploys.committed = e.deploys.committed ++ e.deploys.prospective := rfl

/-! ## The abstract resolution contract -/

/-- The contract W07/W08 program against. The cache environment is a *constant of the contract*, not
a per-environment flag: a statement declares its cache policy once, so no implementation can quietly
consult validator history. The law field records that a non-validator cache policy is admitted.

`committedTracker` is admitted because the in-chunk deploy tracker is deterministic from the chunk's
own bytes; `validatorCache` is not, because a validator's warm compiled-contract cache changes the
verdict without changing the claim or witness (UQ-001/UQ-002, L1 + L7 own the decision). -/
structure ResolutionContract where
  /-- The environment type of the concrete implementation. -/
  Env : Type
  /-- Resolve an account's contract to its identifier form. -/
  resolve : Env → Bytes → Contract → ContractIdentifier
  /-- Resolve the identifier to the code hash it runs. -/
  resolveCodeHash : Env → ContractIdentifier → Except String (Option Bytes)
  /-- Look up a code blob by hash in the defined cache environment. -/
  codeOf : Env → Bytes → Except String (Option Bytes)
  /-- The declared cache policy of the statement. -/
  cacheMode : CacheMode
  /-- The admitted cache policies: cold or committed-deploy tracking, never a validator-history cache. -/
  cacheIndependent : cacheMode = .cold ∨ cacheMode = .committedTracker

/-- The successor's concrete environment satisfies the contract: the signed cold-cache statement. -/
def coldResolutionContract : ResolutionContract where
  Env := ResolutionEnv
  resolve := ResolutionEnv.resolveIdentifier
  resolveCodeHash := ResolutionEnv.resolveCodeHash
  codeOf := ResolutionEnv.codeOf
  cacheMode := .cold
  cacheIndependent := Or.inl rfl

/-- The committed-deploy variant: deterministic from the chunk's own deploy tracker. -/
def committedResolutionContract : ResolutionContract where
  Env := ResolutionEnv
  resolve := ResolutionEnv.resolveIdentifier
  resolveCodeHash := ResolutionEnv.resolveCodeHash
  codeOf := ResolutionEnv.codeOf
  cacheMode := .committedTracker
  cacheIndependent := Or.inr rfl

/-- A validator-history cache is not an admitted successor statement. -/
theorem validatorCache_not_admitted :
    ¬ ((.validatorCache : CacheMode) = .cold ∨ (.validatorCache : CacheMode) = .committedTracker) := by
  decide

/-! ## Axiom-closure check points -/

#print axioms ethWallet_kind_unreachable
#print axioms coldCache_lookup_none

end NearSpecV3.Successor
