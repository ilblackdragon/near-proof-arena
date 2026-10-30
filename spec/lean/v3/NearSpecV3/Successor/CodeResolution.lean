import NearSpecV3.D3.FunctionCall

/-!
# Executable contract-code witness policies

A function call runs the code its contract identifier resolves to. A cold validator (empty
compiled-contract cache at the start of the chunk) obtains those bytes from exactly three places
(nearcore 2.13.4, `44f7ae6c`):

1. **The witness.** A validator requests every code hash in the chunk's `ChunkContractAccesses` that
   is not in its compiled cache and merges the `ContractCodeResponse` into the main transition's
   base state (`partial_witness_actor.rs:696-746`, `partial_witness_tracker.rs:693-696`). The
   producer records an access exactly when the chunk's **pre-state** contract key holds the called
   hash (`record_contract_call`, `function_call.rs:355-393`, a `NO_SIDE_EFFECTS` read), so the
   canonical cold witness carries the bytes of every such call. The partial storage is indexed by
   value hash, so witness bytes are authenticated by their own hash.
2. **The deploy tracker.** `ContractStorage::get` returns uncommitted, then committed in-chunk
   deploys before reading storage (`core/store/src/contract.rs:42-131`). Rollback clears only the
   uncommitted ones.
3. **The compiled cache warmed in this chunk.** `action_deploy_contract` precompiles every deploy
   synchronously, including one later rolled back (`actions.rs:297-339`); the runner consults the
   cache before asking for bytes (`wasmtime_runner/mod.rs:699-724`).

Sources 2 and 3 serve a call deterministically unless its preparation was submitted to the
`ReceiptPreparationPipeline` worker before the serving deploy ran (`pipelining.rs:152-424`); that
is a thread race and nearcore's own verdict is then timing-dependent (`Pipeline.Pipe.deterministic`,
passed in as `timely`). A deploy in the call's own receipt blocks its receiver from pipelining
(`pipelining.rs:176-190`), so it never races.

Two policies:

* `coldPartial` — the cold validator on exactly the given bytes; a race is out of domain.
* `complete` — the same deterministic resolution, plus one authenticated witness rule: when the
  call is a recorded contract access (`PrestateCode.recorded`: the pre-state probe, authenticated
  by the pre-state root, shows the key holds the called hash) the canonical witness carries its
  bytes, so a witness that omits them **and** whose verdict would then hinge on a race is rejected
  as incomplete (`w.code_complete`) instead of excluded. Everywhere else the two policies give the
  same result (`complete_eq_cold_of_timely`, `complete_ok_iff_cold_ok`,
  `complete_differs_only_on_recorded_race`).

Neither policy reads a validator-history cache. UQ-001 (what this means for the compiled-code
cache) is dispositioned in `docs/evidence/lean-chunk-completion/w08-warm-cache/README.md`; the
source audit is `docs/research/lean-code-witness-closure.md`.
-/
namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

inductive CodeWitnessPolicy where
  /-- nearcore's cold validator: in-chunk deploys serve missing code unless preparation raced. -/
  | coldPartial
  /-- The cold validator, with a race on a recorded access decided by the canonical witness. -/
  | complete
  deriving DecidableEq, Repr

/-- The no-side-effect pre-state probe must retain the difference between an absent key and a
path the witness did not reveal. Treating both as `none` would let an unrevealed path pass for
known absence. -/
inductive PrestateCode where
  | absent
  | present (hash : Bytes)
  | unknown
  deriving DecidableEq, Repr

/-- `record_contract_call`'s read uses the actual local/global contract key and no recorder effects.
An unresolved path does not establish that the contract was deployed in this chunk. -/
def prestateCode (trie : PTrie) (key : Bytes) : PrestateCode :=
  match trie with
  | .hash hash => if hash == emptyRoot then .absent else .unknown
  | _ => match trie.findRef (nibbles key) with
    | none => .unknown
    | some none => .absent
    | some (some slot) => .present (slot.valueRef.drop 4)

def PrestateCode.hash? : PrestateCode → Option Bytes
  | .present h => some h
  | _ => none

/-- nearcore's `record_contract_call` (`function_call.rs:355-393`): the call is a contract access,
and its code is part of the canonical cold witness, exactly when the pre-state contract key holds
the called hash. `unknown` (the witness does not reveal the path) is *not* evidence either way. -/
def PrestateCode.recorded (pre : PrestateCode) (hash : Bytes) : Bool :=
  match pre with
  | .present h => h == hash
  | _ => false

/-- Bytes in these lists come from executed authenticated deploy/distribution actions. Rollback
clears `current`; it never promotes failed deploys into `committed`. `attempted` (every executed
deploy, committed or rolled back) is what the chunk's own precompiles put in the compiled cache. -/
structure CodeSources where
  witness : Bytes → Option Bytes
  current : List Bytes := []
  committed : List Bytes := []
  attempted : List Bytes := []

/-- The complete policy's one extra reject: a recorded access whose bytes the witness omits, where
nearcore would otherwise have to win a preparation race to find the code. -/
def incompleteCodeWitness : String :=
  "invalid witness (w.code_complete): the witness omits the code of a recorded pre-state contract access that only a racing in-chunk deploy could serve"

def unauthenticatedCodeWitness : String :=
  "invalid witness (w.code_complete): contract code does not hash to the resolved identifier"

/-- nearcore's cold `MissingTrieValue` for a call whose code no source holds (`function_call.rs:293-305`). -/
def missingCode : String := "invalid: MissingTrieValue (contract code)"

/-- The pipeline-race exclusion (`Pipeline`): nearcore's own verdict is timing-dependent. Its code
names the cause, a preparation race against an in-chunk deploy; until 2026-10-29 it was reported
under the generic `e.wasm-α`, and the generator labelled the same cases `e.code_cache`. -/
def raceExclusion : String :=
  "out of domain (e.code_prep_race): contract preparation pipelined before the in-chunk deploy that serves its code"

/-- The cold validator (`ContractStorage::get`, `contract.rs:104-128`, behind the compiled-contract
cache). Code not in the witness can still be served by a deploy earlier in this chunk: the deploy
tracker holds uncommitted and committed deploys, and `action_deploy_contract` precompiles every
deploy into the compiled cache, so a rolled-back one (`attempted`) is still a cache hit for the
same hash. Whether a *pipelined* preparation sees it depends on when it was submitted:
`timely` is `Pipeline.deterministic`, false when the task was submitted before every deploy of
this code finished, which is a thread race in nearcore and therefore out of domain.

A deploy in the call's own receipt (`current`) blocks the receiver from pipelining, so it never
races. The pre-state probe plays no part: nearcore's validator never reads the code key. -/
def resolveColdCode (sources : CodeSources) (timely : Bool) (hash : Bytes) : Except String Bytes :=
  match sources.witness hash with
  | some code => .ok code
  | none =>
    match sources.current.find? (fun code => sha256 code == hash) with
    | some code => .ok code
    | none =>
      match (sources.committed ++ sources.attempted).find? (fun code => sha256 code == hash) with
      | some code => if timely then .ok code else .error raceExclusion
      | none => .error missingCode

/-- The complete-code relation. The same resolution as `resolveColdCode`, except that (a) witness
bytes are hash-checked explicitly, independently of how the store was built, and (b) a race on a
recorded access is a witness reject, not an exclusion: the canonical witness carries those bytes
(`PrestateCode.recorded`), so the verdict rests on that authenticated input instead of on thread
timing. A race on an unrecorded or unrevealed access stays out of domain. -/
def resolveCompleteCode (sources : CodeSources) (pre : PrestateCode) (timely : Bool) (hash : Bytes) :
    Except String Bytes :=
  match sources.witness hash with
  | some code =>
    if sha256 code == hash then .ok code else .error unauthenticatedCodeWitness
  | none =>
    match sources.current.find? (fun code => sha256 code == hash) with
    | some code => .ok code
    | none =>
      match (sources.committed ++ sources.attempted).find? (fun code => sha256 code == hash) with
      | some code =>
        if timely then .ok code
        else if pre.recorded hash then .error incompleteCodeWitness
        else .error raceExclusion
      | none => .error missingCode

def resolveCodeBytes (policy : CodeWitnessPolicy) (sources : CodeSources)
    (pre : PrestateCode) (hash : Bytes) (timely : Bool := true) : Except String Bytes :=
  match policy with
  | .coldPartial => resolveColdCode sources timely hash
  | .complete => resolveCompleteCode sources pre timely hash

/-- Witness bytes are indexed by their own hash (`mkHStore`; nearcore's partial storage). -/
def CodeSources.authentic (sources : CodeSources) (hash : Bytes) : Prop :=
  ∀ code, sources.witness hash = some code → sha256 code = hash

/-- A raw code blob, authenticated against the requested hash, makes origin, deployment history
and preparation timing irrelevant to code selection. -/
theorem complete_supplied (sources : CodeSources) (pre : PrestateCode) (code hash : Bytes)
    (timely : Bool) (found : sources.witness hash = some code) (auth : sha256 code = hash) :
    resolveCodeBytes .complete sources pre hash timely = .ok code := by
  simp [resolveCodeBytes, resolveCompleteCode, found, auth]

/-- When the preparation schedule cannot race (`timely`), the complete policy **is** the cold
validator on authenticated witness bytes: the same code or the same error string. -/
theorem complete_eq_cold_of_timely (sources : CodeSources) (pre : PrestateCode) (hash : Bytes)
    (auth : sources.authentic hash) :
    resolveCodeBytes .complete sources pre hash true =
      resolveCodeBytes .coldPartial sources pre hash true := by
  unfold resolveCodeBytes resolveCompleteCode resolveColdCode
  cases hw : sources.witness hash with
  | some code => simp [auth code hw]
  | none => simp

/-- Under authenticated witness bytes the two policies accept exactly the same calls with the same
code, on every schedule. -/
theorem complete_ok_iff_cold_ok (sources : CodeSources) (pre : PrestateCode) (hash code : Bytes)
    (timely : Bool) (auth : sources.authentic hash) :
    resolveCodeBytes .complete sources pre hash timely = .ok code ↔
      resolveCodeBytes .coldPartial sources pre hash timely = .ok code := by
  unfold resolveCodeBytes resolveCompleteCode resolveColdCode
  cases hw : sources.witness hash with
  | some c => simp [auth c hw]
  | none =>
    cases sources.current.find? (fun code => sha256 code == hash) with
    | some c => simp
    | none =>
      cases (sources.committed ++ sources.attempted).find? (fun code => sha256 code == hash) with
      | none => simp
      | some c => cases timely <;> cases pre.recorded hash <;> simp

/-- The only place the policies differ: a racing preparation on a recorded access, which the
complete policy rejects and the cold policy excludes. -/
theorem complete_differs_only_on_recorded_race (sources : CodeSources) (pre : PrestateCode)
    (hash : Bytes) (timely : Bool) (auth : sources.authentic hash)
    (hne : resolveCodeBytes .complete sources pre hash timely ≠
      resolveCodeBytes .coldPartial sources pre hash timely) :
    timely = false ∧ pre.recorded hash = true ∧
      resolveCodeBytes .complete sources pre hash timely = .error incompleteCodeWitness ∧
      resolveCodeBytes .coldPartial sources pre hash timely = .error raceExclusion := by
  revert hne
  unfold resolveCodeBytes resolveCompleteCode resolveColdCode
  cases hw : sources.witness hash with
  | some c => simp [auth c hw]
  | none =>
    cases sources.current.find? (fun code => sha256 code == hash) with
    | some c => simp
    | none =>
      cases (sources.committed ++ sources.attempted).find? (fun code => sha256 code == hash) with
      | none => simp
      | some c => cases timely <;> cases pre.recorded hash <;> simp

end NearSpecV3.Successor
