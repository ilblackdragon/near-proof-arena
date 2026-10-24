import NearSpecV3.D3.FunctionCall

/-!
# Executable contract-code witness policies

The historical cold/partial-witness relation can depend on asynchronous preparation after a
same-code deploy, including a rolled-back deploy. `complete` is a different, explicit witness
boundary: every pre-state or unresolved-origin call supplies its raw code by authenticated hash.
No compiled artifact, cache-hit bit or preparation result is a witness input.

This policy rejects an incomplete **witness**, not a protocol chunk that a warm validator might
execute. It is not an equivalence theorem with nearcore's cold validator on missing-code mutants.
See `docs/research/lean-code-witness-closure.md` for the pinned source audit and relation contract.
-/
namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

inductive CodeWitnessPolicy where
  /-- Preserve the earlier successor's explicit cache-dependent exclusion. -/
  | coldPartial
  /-- Reject incomplete code witnesses; execution never relies on external cache history. -/
  | complete
  deriving DecidableEq, Repr

/-- The no-side-effect pre-state probe must retain the difference between an absent key and a
path the witness did not reveal. Treating both as `none` can bypass code completeness. -/
inductive PrestateCode where
  | absent
  | present (hash : Bytes)
  | unknown
  deriving DecidableEq, Repr

/-- `record_contract_call`'s read uses the actual local/global contract key and no recorder effects.
An unresolved path does not establish that the contract was deployed in this chunk. -/
def prestateCode (trie : PTrie) (key : Bytes) : PrestateCode :=
  if trie.hashOf == emptyRoot then .absent else
  match trie.findRef (nibbles key) with
  | none => .unknown
  | some none => .absent
  | some (some slot) => .present (slot.valueRef.drop 4)

def PrestateCode.hash? : PrestateCode → Option Bytes
  | .present h => some h
  | _ => none

/-- Unknown origin conservatively requires raw witness code. A changed/absent pre-state code can
use the current or committed deploy tracker (same-account identity changes block preparation). -/
def PrestateCode.needsWitness (pre : PrestateCode) (hash : Bytes) : Bool :=
  match pre with
  | .unknown => true
  | .absent => false
  | .present h => h == hash

/-- Bytes in these lists come from executed authenticated deploy/distribution actions. Rollback
clears `current`; it never promotes failed deploys into `committed`. `attempted` is used only by
`coldPartial`, to conservatively exclude cache/preparation-dependent missing-code cases. -/
structure CodeSources where
  witness : Bytes → Option Bytes
  current : List Bytes := []
  committed : List Bytes := []
  attempted : List Bytes := []

def CodeSources.deployed (sources : CodeSources) (hash : Bytes) : Option Bytes :=
  (sources.current ++ sources.committed).find? (fun code => sha256 code == hash)

/-- The prefix is a typed witness-policy failure for the explicit complete-code relation. -/
def incompleteCodeWitness : String :=
  "invalid witness (w.code_complete): raw contract code is required for pre-state or unresolved-origin execution"

def unauthenticatedCodeWitness : String :=
  "invalid witness (w.code_complete): contract code does not hash to the resolved identifier"

/-- Historical behavior, factored out without changing its missing-code or exclusion strings. -/
def resolveColdCode (sources : CodeSources) (pre : PrestateCode) (hash : Bytes) : Except String Bytes :=
  match sources.witness hash with
  | some code => .ok code
  | none =>
    if pre.hash? == some hash then
      if (sources.current ++ sources.committed ++ sources.attempted).any (fun code => sha256 code == hash) then
        .error (D3.oodE "pre-state contract served only by the in-chunk compiled-contract cache")
      else .error "invalid: MissingTrieValue (contract code)"
    else match sources.deployed hash with
      | some code => .ok code
      | none => .error "invalid: MissingTrieValue (contract code)"

/-- The complete-witness decision does not read `attempted` or any compiled cache. Raw witness
code is checked even if the store implementation is not `mkHStore`; production stores are built
from content hashes. Deployment candidates are individually hash-checked by `deployed`. -/
def resolveCompleteCode (sources : CodeSources) (pre : PrestateCode) (hash : Bytes) : Except String Bytes :=
  match sources.witness hash with
  | some code =>
    if sha256 code == hash then .ok code else .error unauthenticatedCodeWitness
  | none =>
    if pre.needsWitness hash then .error incompleteCodeWitness
    else match sources.deployed hash with
      | some code => .ok code
      | none => .error "invalid witness (w.code_complete): no authenticated code in witness or committed deployment"

def resolveCodeBytes (policy : CodeWitnessPolicy) (sources : CodeSources)
    (pre : PrestateCode) (hash : Bytes) : Except String Bytes :=
  match policy with
  | .coldPartial => resolveColdCode sources pre hash
  | .complete => resolveCompleteCode sources pre hash

/-- Changing attempted (including rolled-back) deployments cannot change a complete-code verdict.
This is an implementation law, not an assumed cache-independence field. -/
theorem complete_attempted_independent (sources : CodeSources) (attempted : List Bytes)
    (pre : PrestateCode) (hash : Bytes) :
    resolveCodeBytes .complete { sources with attempted } pre hash =
      resolveCodeBytes .complete sources pre hash := rfl

/-- A raw code blob, authenticated against the requested hash, makes origin and deployment
history irrelevant to code selection (and therefore to preparation's ability to load the bytes). -/
theorem complete_supplied (sources : CodeSources) (pre : PrestateCode) (code hash : Bytes)
    (found : sources.witness hash = some code) (auth : sha256 code = hash) :
    resolveCodeBytes .complete sources pre hash = .ok code := by
  simp [resolveCodeBytes, resolveCompleteCode, found, auth]

theorem complete_unknown_requires_witness (sources : CodeSources) (hash : Bytes)
    (absent : sources.witness hash = none) :
    resolveCodeBytes .complete sources .unknown hash = .error incompleteCodeWitness := by
  simp [resolveCodeBytes, resolveCompleteCode, absent, PrestateCode.needsWitness]

theorem complete_prestate_requires_witness (sources : CodeSources) (hash : Bytes)
    (absent : sources.witness hash = none) :
    resolveCodeBytes .complete sources (.present hash) hash = .error incompleteCodeWitness := by
  simp [resolveCodeBytes, resolveCompleteCode, absent, PrestateCode.needsWitness]

end NearSpecV3.Successor
