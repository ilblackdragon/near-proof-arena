import NearSpecV3.D2.Receipts

/-!
# The receipt preparation pipeline, as far as it decides code availability

A cold validator can execute a pre-state contract whose code is not in the witness when a deploy of
the same code ran earlier in the chunk: `action_deploy_contract` precompiles the code into the
compiled-contract cache unconditionally (`actions.rs:297-339`), and a committed deploy also stays
in the deploy tracker (`contract.rs:42-69`). Whether the later call sees either depends on *when
its preparation started*. `ReceiptPreparationPipeline::submit` (`pipelining.rs:152-310`) hands a
function call to a worker thread, which looks the code up immediately; the main thread only
prepares it itself when the call was never submitted or the worker has not started
(`get_contract`, `pipelining.rs:323-424`). A worker that ran before the deploy finds neither the
cache entry nor the tracker entry and the validator fails with `MissingTrieValue`
(`function_call.rs:293-305`). That is a thread race, not a protocol rule.

Submission happens on the main thread between receipts, staggered by one "interesting" receipt
(`schedule_contract_preparation`, `lib.rs:3256-3324`, driven from the local/delayed/incoming loops
at `lib.rs:2357-2610`). So the race exists exactly when the call's task was submitted no later than
the start of the receipt that ran the deploy. This module replays that schedule over the same
partial state the validator has, so a missing-code call served by an in-chunk deploy is either
deterministic (task submitted after the deploy's receipt finished, or never submitted) or racy.

Lookups here are nearcore's `NO_SIDE_EFFECTS` reads (`get_pure`): they read the overlay and the
revealed pre-state, record nothing, and a value the witness does not reveal is an error that
skips the receipt, exactly as it does in the validator. Shapes this module does not model (a call
on a global contract identity, a stored receipt it cannot decode) set `uncertain`; a resolution
that depends on timing after that is out of domain.
-/
namespace NearSpecV3.Successor.Pipeline
open NearSpec NearSpecV3 NearSpecV3.D2

/-- A `PrepareTask`: its `PrepareTaskKey` (receipt, action index), the expected code hash and the
main-thread clock (receipts started so far) at submission. -/
structure Task where
  rid : Bytes
  idx : Nat
  code : Bytes
  submitted : Nat
  deriving Repr

structure Pipe where
  /-- Receipts whose processing the main thread has started. -/
  clock : Nat := 0
  /-- The clock value at the start of the receipt now executing. -/
  current : Nat := 0
  /-- `block_accounts`. -/
  blocked : List Bytes := []
  tasks : List Task := []
  uncertain : Bool := false
  /-- `(sha256 code, clock at the start of the deploying receipt)` for every executed deploy. -/
  deploys : List (Bytes × Nat) := []
  /-- The current list phase: the lookahead not yet scanned and `next_schedule_after`. -/
  look : List Rcpt := []
  next : Option Nat := none
  deriving Repr

/-- `get_pure`: `none` when the witness does not reveal the value (an `Err` in nearcore). -/
def peek (o : Ovl) (k : Bytes) : Option (Option Bytes) :=
  match o.lookup k with
  | some v => some v
  | none => o.trie.find (nibbles k)

/-- `submit` over the actions of one action or yield receipt (`pipelining.rs:172-308`). -/
def submitActions (o : Ovl) (rid recv : Bytes) :
    Pipe → Option (Option Acct) → Nat → Bool → List Act → Pipe × Bool
  | p, _, _, any, [] => (p, any)
  | p, acct, i, any, a :: rest =>
    match a with
    | .base ⟨_, .deploy _⟩ | .base ⟨_, .useGlobal _⟩ | .base ⟨_, .stateInit _⟩
    | .base ⟨_, .createAccount⟩ | .base ⟨_, .deleteAccount _⟩ =>
      -- every code-identity change blocks the receiver; `insert` is new (checked by the caller)
      ({ p with blocked := p.blocked ++ [recv] }, true)
    | .base ⟨_, .fcall _ _ _ _⟩ =>
      let (p, acct) := match acct with
        | some x => (p, x)
        | none => match peek o (kAccount recv) with
          | some (some raw) => match decodeAcct raw with
            | some x => (p, some x)
            | none => ({ p with uncertain := true }, none)
          | _ => (p, none)
      match acct with
      | none => submitActions o rid recv p (some none) (i + 1) any rest
      | some x => match x.contract with
        | .none => submitActions o rid recv p (some (some x)) (i + 1) any rest
        | .local h =>
          if p.tasks.any (fun t => t.rid == rid && t.idx == i) then
            submitActions o rid recv p (some (some x)) (i + 1) any rest
          else
            let p := { p with tasks := p.tasks ++ [⟨rid, i, h, p.clock⟩] }
            submitActions o rid recv p (some (some x)) (i + 1) true rest
        | _ => submitActions o rid recv { p with uncertain := true } (some (some x)) (i + 1) any rest
    | _ => submitActions o rid recv p acct (i + 1) any rest

def submitRcpt (o : Ovl) (p : Pipe) (r : Rcpt) : Pipe × Bool :=
  if p.blocked.contains r.recv then (p, false) else
  match r.body with
  | .action _ a => submitActions o r.rid r.recv p none 0 false a.actions
  | _ => (p, false)

/-- The scheduler's `handle_receipt` (`lib.rs:3264-3320`): a data receipt that completes a
postponed receipt, or a resume, submits the receipt it releases. `decode` is the stored-receipt
decoder of the active codec. -/
def handle (decode : Bytes → Except String Rcpt) (o : Ovl) (p : Pipe) (r : Rcpt) : Pipe × Bool :=
  let stored (k : Bytes) : Pipe × Bool :=
    match peek o k with
    | some (some b) => match decode b with
      | .ok x => submitRcpt o p x
      | .error _ => ({ p with uncertain := true }, false)
    | _ => (p, false)
  match r.body with
  | .action _ _ => submitRcpt o p r
  | .data false d _ =>
    match peek o (kPostponedId r.recv d) with
    | some (some rid) =>
      match peek o (kPendingCount r.recv rid) with
      | some (some c) => match decodeU32 c with
        | some n => if n > 1 then (p, false) else stored (kPostponed r.recv rid)
        | none => (p, false)
      | _ => (p, false)
    | _ => (p, false)
  | .data true d _ => stored (kYieldReceipt r.recv d)
  | .distribution _ => (p, false)

/-- `schedule_contract_preparation`: submit lookahead receipts until one may have scheduled work;
returns the remaining lookahead and `Some (position + 1)`. -/
def schedule (decode : Bytes → Except String Rcpt) (o : Ovl) : Pipe → List Rcpt → Pipe × List Rcpt × Option Nat
  | p, [] => (p, [], none)
  | p, r :: rest =>
    let (p, ok) := handle decode o p r
    if ok then (p, rest, some 1) else
    let (p, rest, n) := schedule decode o p rest
    (p, rest, n.map (· + 1))

/-- Start a list phase (local or incoming receipts). -/
def startList (decode : Bytes → Except String Rcpt) (o : Ovl) (p : Pipe) (rs : List Rcpt) : Pipe :=
  let (p, look, next) := schedule decode o p rs
  { p with look, next }

/-- Before the main thread processes the next receipt of a list phase. -/
def stepList (decode : Bytes → Except String Rcpt) (o : Ovl) (p : Pipe) : Pipe :=
  match p.next with
  | none => p
  | some n =>
    if n - 1 == 0 then
      let (p, look, next) := schedule decode o p p.look
      { p with look, next }
    else { p with next := some (n - 1) }

/-- `DelayedReceiptQueueWrapper::peek_iter` (`congestion_control.rs:912-920`): stored delayed
receipts from `first`, stopping at the first unreadable entry, skipping other shards' receipts. -/
def peekDelayed (decodeStored : Bytes → Except String Stored) (layout : Layout) (own : Nat)
    (o : Ovl) (p : Pipe) : Nat → Nat → Nat → Pipe × List Rcpt
  | 0, _, _ => (p, [])
  | fuel + 1, i, next =>
    if i ≥ next then (p, []) else
    match peek o (kDelayed i) with
    | some (some b) => match decodeStored b with
      | .ok st =>
        let (p, rest) := peekDelayed decodeStored layout own o p fuel (i + 1) next
        (p, if st.r.targetShard layout == own then st.r :: rest else rest)
      | .error _ => ({ p with uncertain := true }, [])
    | _ => (p, [])

/-- The main thread starts a receipt: advance the clock. -/
def startReceipt (p : Pipe) : Pipe := { p with current := p.clock, clock := p.clock + 1 }

def Pipe.recordDeploys (p : Pipe) (codes : List Bytes) : Pipe :=
  { p with deploys := p.deploys ++ codes.map fun c => (sha256 c, p.current) }

/-- Whether code served by an in-chunk deploy reaches the call `(rid, idx)` deterministically:
its preparation was never submitted (or for another code hash, so it is redone on the main
thread), or it was submitted after some deploy of `hash` had finished. -/
def Pipe.deterministic (p : Pipe) (rid : Bytes) (idx : Nat) (hash : Bytes) : Bool :=
  !p.uncertain &&
  match p.tasks.find? (fun t => t.rid == rid && t.idx == idx && t.code == hash) with
  | none => true
  | some t => p.deploys.any fun (h, s) => h == hash && s < t.submitted

end NearSpecV3.Successor.Pipeline
