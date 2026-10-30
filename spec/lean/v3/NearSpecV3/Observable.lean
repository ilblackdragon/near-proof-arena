import NearSpecV3.RuntimeD1
import NearSpecV3.D2.Types

/-!
# `NearSpecV3.Observable` — the consensus outputs a chunk transition produces

The signed checkers (`checkD2`, `checkD3`) compute the whole chunk transition and then *compare*
every consensus output against the endorsed header's fields — but they return only
`Except String Unit`, so the outputs themselves never leave the checker. This module gives those
outputs a name and a single record type so a checker variant can return them, and so a differential
report can compare them field by field.

## Why this module sits below `ChunkValidationD2`

`Successor/Differential.lean` already has an `Observable` vocabulary, but it imports
`Successor/Config.lean`, which imports `ChallengeChunkV3Gas`, which imports `ChunkValidationD2`. A
checker in `ChunkValidationD2` that returned `Differential.Observable` would close an import cycle.
This module imports only `RuntimeD1` and `D2/Types`, both of which sit below `ChunkValidationD2`, so
the checker can depend on it. `Differential.Observable` remains the *report* vocabulary; the record
here is the *checker* output, and `toDifferential` bridges them.

## What the fields mean

Each field is the value the checker computed and compared against the endorsed chunk header. The
header's own value came from nearcore when it applied the chunk, so an accepted case's record is a
statement about agreement with nearcore, not just an internal self-consistency check.

* `stateRoot` — the post-state root after the main transition and every implicit transition; compared
  against `prev_state_root`.
* `outcomeRoot` — `merklize(outcomes.to_hashes())`; compared against `prev_outcome_root`.
* `gasBurnt` — `Σ outcome.gas_burnt` over the chunk's outcomes; compared against `prev_gas_used`.
* `balanceBurnt` — tx + other − subsidized; compared against `prev_balance_burnt`.
* `outgoingReceiptsRoot` — the outgoing receipts root; compared against `prev_outgoing_receipts_root`.
* `proposals` — the deduplicated validator proposals; compared against the header's proposals.
* `txRoot` — `merklize(txs)` of the last new chunk; compared against `tx_root`.
* `encodedMerkleRoot` / `encodedLength` — the Reed–Solomon encoded chunk body; compared against the
  header's fields.
* `congestion`, `bwRequests` — compared against the header's congestion info and bandwidth requests.
* `logs` — every executed outcome's logs in order. These are folded into `outcomeRoot`; the separate
  field lets a report show them without re-deriving the merkle path.
* `receiptCount` — the number of outgoing receipts. Also folded into `outgoingReceiptsRoot`.

## What is not established

* **Nothing here runs a checker.** This is a type and a bridge.
* **`logs` is a projection of `outcomes`, not an independent computation.** A report that compares
  `logs` and `outcomeRoot` separately is comparing one computed value with another, not two runs.
* **No field here is derived from a witness.** Every value is computed by the checker from the claim
  and witness; the only nearcore-produced values involved are the header fields the checker compares
  against.
-/

namespace NearSpecV3

open NearSpec

/-- The consensus-visible outputs of one chunk transition: the values `checkD2Core` computes and
validates against the endorsed header. -/
structure Observable where
  /-- Post-state root after the main and all implicit transitions (`H.prevStateRoot`). -/
  stateRoot : Bytes
  /-- `merklize(outcomes.to_hashes())` (`H.prevOutcomeRoot`). -/
  outcomeRoot : Bytes
  /-- `Σ outcome.gas_burnt` over the chunk's outcomes (`H.prevGasUsed`). -/
  gasBurnt : Nat
  /-- `tx_burnt + other_burnt − subsidized` (`H.prevBalanceBurnt`). -/
  balanceBurnt : Nat
  /-- The outgoing receipts root (`H.prevOutgoingReceiptsRoot`). -/
  outgoingReceiptsRoot : Bytes
  /-- The deduplicated validator proposals, encoded (`H.proposals`). -/
  proposals : List Bytes
  /-- `merklize(txs)` of the last new chunk (`H.txRoot`). -/
  txRoot : Bytes
  /-- Reed–Solomon encoded chunk body merkle root (`H.encodedMerkleRoot`). -/
  encodedMerkleRoot : Bytes
  /-- Reed–Solomon encoded chunk body length (`H.encodedLength`). -/
  encodedLength : Nat
  /-- Chunk congestion info (`H.congestion`). -/
  congestion : Congestion
  /-- Bandwidth requests (`H.bwRequests`). -/
  bwRequests : List BwRequest
  /-- Every executed outcome's logs, in execution order. Folded into `outcomeRoot`; shown separately. -/
  logs : List Bytes
  /-- The number of outgoing receipts. Folded into `outgoingReceiptsRoot`; shown separately. -/
  receiptCount : Nat
  /-- Σ `gas_burnt_for_function_call` of the chunk (the D3 cap's measured quantity). -/
  wasmGas : Nat
  /-- Every executed outcome, in execution order: the list `outcomeRoot` merklizes (W01). Empty when
  a checker does not report it (the D1/D2 out-drivers). -/
  outcomes : List OutD1 := []
  /-- The outgoing receipts, in order: the list `outgoingReceiptsRoot` commits to. -/
  outgoing : List D2.Rcpt := []
  /-- The main transition's committed storage changes at `finalize` (ascending raw trie key,
  `none` = deleted), rollbacks applied. `none` when the driver does not report it. -/
  stateChanges : Option (List (Bytes × Option Bytes)) := none
  /-- Σ compute usage of the main transition's outcomes, when reported. -/
  computeUsage : Option Nat := none
  /-- Failure kinds, per-outcome compute and per-receipt storage attribution, when reported
  (observation only, W01). -/
  detail : Option D2.ObsDetail := none
  deriving Repr

/-- The outputs a D2-domain chunk reports: the D3-only fields are `0`. -/
def Observable.ofD2 (stateRoot outcomeRoot outgoingReceiptsRoot txRoot encodedMerkleRoot : Bytes)
    (gasBurnt balanceBurnt encodedLength receiptCount : Nat)
    (proposals : List Bytes) (congestion : Congestion) (bwRequests : List BwRequest)
    (logs : List Bytes) : Observable :=
  { stateRoot, outcomeRoot, gasBurnt, balanceBurnt, outgoingReceiptsRoot, proposals, txRoot,
    encodedMerkleRoot, encodedLength, congestion, bwRequests, logs, receiptCount, wasmGas := 0 }

/-- **The header agreement predicate.** `checkD2Core`'s header comparison block, as one predicate over
the computed outputs and the endorsed header's fields. An accepted case satisfies this by construction;
splitting it out lets a report say *which* field disagreed when it does not.

This is a restatement of the checks at `ChunkValidationD2.lean:254-266`, not a new condition: each
conjunct is one of those `check`s. -/
def Observable.agreesWithHeader (o : Observable) (prevStateRoot prevOutcomeRoot : Bytes)
    (prevGasUsed prevBalanceBurnt : Nat) (prevOutgoingReceiptsRoot txRoot encodedMerkleRoot : Bytes)
    (encodedLength : Nat) (proposals : List Bytes) (congestion : Congestion)
    (bwRequests : List BwRequest) : Bool :=
  o.stateRoot == prevStateRoot ∧ o.outcomeRoot == prevOutcomeRoot ∧
  o.gasBurnt == prevGasUsed ∧ o.balanceBurnt == prevBalanceBurnt ∧
  o.outgoingReceiptsRoot == prevOutgoingReceiptsRoot ∧ o.proposals == proposals ∧
  o.congestion == congestion ∧ o.bwRequests == bwRequests ∧ o.txRoot == txRoot ∧
  o.encodedMerkleRoot == encodedMerkleRoot ∧ o.encodedLength == encodedLength

theorem agreesWithHeader_refl (o : Observable) :
    o.agreesWithHeader o.stateRoot o.outcomeRoot o.gasBurnt o.balanceBurnt
      o.outgoingReceiptsRoot o.txRoot o.encodedMerkleRoot o.encodedLength o.proposals
      o.congestion o.bwRequests = true := by
  simp [Observable.agreesWithHeader]

/-- If a computed field equals one header value and that header value equals another, the field equals
the second. Used when a report compares against a header it decoded twice. -/
theorem agreesWithHeader_congr (o : Observable) (a b : Bytes) :
    o.stateRoot = a → a = b → (o.stateRoot == b) = true := by
  intro h1 h2; rw [← h2, h1]; simp

#print axioms agreesWithHeader_refl
#print axioms agreesWithHeader_congr

end NearSpecV3
