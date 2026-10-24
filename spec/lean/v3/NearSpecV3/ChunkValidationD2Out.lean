import NearSpecV3.Observable
import NearSpecV3.ChunkValidationD2

/-!
# `NearSpecV3.ChunkValidationD2Out` — the transition returning its outputs

`checkD2Core` (`ChunkValidationD2.lean:114`) computes the whole chunk transition and validates every
consensus output against the endorsed header, then returns `Except String Unit`: the outputs are
compared and discarded. This module returns them.

## Design: accept first, then emit — so acceptance is definitional

`checkD2CoreOut` runs the **signed** checker `checkD2Core` and, only when it accepts, decodes the claim
and returns the endorsed header's consensus fields as an `Observable`.

That ordering is what makes the agreement theorem free rather than a re-derivation:

* `checkD2CoreOut` accepts **iff** `checkD2Core` accepts — by construction, because the first thing it
  does is call it. There is no second pipeline to keep in step, so there is nothing to drift.
* The emitted values are the header's. `checkD2Core`'s header comparison block
  (`ChunkValidationD2.lean:254-266`) asserts, field by field, that the header's value **equals the value
  the pipeline computed** — `H.prevGasUsed == out.gasUsed`, `H.prevBalanceBurnt == out.balanceBurnt`,
  `H.prevOutcomeRoot == outcomeRootD1 out.outcomes`, and so on. So on acceptance the header's value *is*
  the computed value. Emitting it is emitting the computed output, justified by the checker's own
  equality checks rather than by a second computation.

## What this buys and what it does not

**Buys.** A run that produces, per accepted case, the consensus outputs — state root, outcome root, gas
burnt, balance burnt, outgoing receipts root, proposals, tx root, encoded merkle root/length, congestion,
bandwidth requests — as data, so a report can put them beside nearcore's. The relation itself is
untouched: no definition in the signed module changes, so every existing proof and every existing
verdict is preserved exactly.

**Does not buy.**

1. **A numeric diff on rejected cases.** Because the outputs come from the header, a rejected case's
   record holds the header's values, not Lean's differing computed values. The *reason string* names the
   field that disagreed (`InvalidGasUsed`, `InvalidBalanceBurnt`, …), which identifies the mismatch but
   does not show both numbers. A numeric diff needs the computed value to escape the pipeline, which
   needs the pipeline refactored (see `var/OUTPUTS-PLAN.md` P1-alternative) — deliberately not done here,
   because the signed `checkD2Core` is unfolded by the `Logged` proof closure
   (`Logged/D2Check.lean:393`) and refactoring it would cascade into `checkD2L_eq`, `checkD3L_eq` and the
   read-set API.
2. **A claim that the pipeline's *internal* computation equals nearcore's.** The header's values were
   produced by nearcore; agreement with them is agreement with nearcore *on those fields*. That is what
   `checkD2Core` already established; this module makes it visible.
3. **Any widening.** `checkD2CoreOut` accepts exactly what `checkD2Core` accepts. It is an observation
   layer, not a successor.

## Axioms

Every theorem here is axiom-free within `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace NearSpecV3

open NearSpec NearSpecV3.D2

/-! ## Decoding the endorsed header's outputs

The claim's `chunkInner` is the endorsed chunk header. Its consensus fields are what `checkD2Core`'s
comparison block validates against the computed transition. -/

/-- The consensus outputs recorded in an endorsed chunk header. This is the *declared* form of the
outputs; `checkD2Core` proves the computed values equal it on acceptance. -/
def Observable.ofChunkInner (H : ChunkInner) (txs : List TxD2) (logs : List Bytes)
    (receiptCount wasmGas : Nat) : Observable :=
  { stateRoot := H.prevStateRoot
    outcomeRoot := H.prevOutcomeRoot
    gasBurnt := H.prevGasUsed
    balanceBurnt := H.prevBalanceBurnt
    outgoingReceiptsRoot := H.prevOutgoingReceiptsRoot
    proposals := H.proposals
    txRoot := H.txRoot
    encodedMerkleRoot := H.encodedMerkleRoot
    encodedLength := H.encodedLength
    congestion := H.congestion
    bwRequests := H.bwRequests
    logs := logs
    receiptCount := receiptCount
    wasmGas := wasmGas }

/-- The outputs an endorsed header declares satisfy the header-agreement predicate by reflexivity. A
report can therefore use this record as the *expected* side and the checker's acceptance as the proof
that the computed side matched it. -/
theorem ofChunkInner_agrees (H : ChunkInner) (txs : List TxD2) (logs : List Bytes)
    (receiptCount wasmGas : Nat) :
    (Observable.ofChunkInner H txs logs receiptCount wasmGas).agreesWithHeader
      H.prevStateRoot H.prevOutcomeRoot H.prevGasUsed H.prevBalanceBurnt H.prevOutgoingReceiptsRoot
      H.txRoot H.encodedMerkleRoot H.encodedLength H.proposals H.congestion H.bwRequests = true := by
  simp [Observable.ofChunkInner, Observable.agreesWithHeader]

/-! ## The output-returning checker -/

/-- Decode the claim's endorsed header. `none` when the claim does not decode — in which case the signed
checker has already failed, so this is only reached on a path where the outputs are not reported. -/
def headerOfClaim (claimBytes : Bytes) : Option ChunkInner :=
  match decodeClaimE claimBytes with
  | .ok c => (decodeChunkInner c.chunkInner).toOption
  | .error _ => none

/-- The claim's endorsed header, if it decodes. Used by the driver to report the *declared* outputs
beside the checker's verdict. -/
def claimHeader? (claimBytes : Bytes) : Option ChunkInner := headerOfClaim claimBytes

theorem claimHeader?_eq (cb : Bytes) : claimHeader? cb = headerOfClaim cb := rfl

/-! ## The theorem that ties the two checkers together

`checkD2CoreOut` *is* `checkD2CoreObs`, the computation the signed checker projects. So the accept/reject
decision is definitionally the signed one, and the emitted record is the computed record — there is no
second pipeline that could disagree and no read-back of the header. -/

/-- The output-returning checker: the signed checker's own computation, returning the record of values
it computed and compared against the endorsed header. Definitionally `checkD2CoreObs`, so the verdict is
the signed verdict and the emitted values are the computed values — not a read-back of the header. -/
def checkD2CoreOut (hooks : ActionHooks) (allowCodes : Bool) (claimBytes witnessBytes : Bytes)
    (gasCap : Option Nat := none) : Except String Observable :=
  checkD2CoreObs hooks allowCodes claimBytes witnessBytes gasCap

/-- **Agreement is definitional.** The output checker is the signed checker's computation. -/
theorem checkD2CoreOut_agrees (hooks : ActionHooks) (allowCodes : Bool) (cb wb : Bytes)
    (gasCap : Option Nat) :
    (∃ o, checkD2CoreOut hooks allowCodes cb wb gasCap = .ok o) ↔
      checkD2Core hooks allowCodes cb wb gasCap = .ok () :=
  checkD2CoreObs_agrees hooks allowCodes cb wb gasCap

/-- A rejection carries the signed checker's error string verbatim. -/
theorem checkD2CoreOut_reject (hooks : ActionHooks) (allowCodes : Bool) (cb wb : Bytes)
    (gasCap : Option Nat) (e : String)
    (h : checkD2CoreOut hooks allowCodes cb wb gasCap = .error e) :
    checkD2Core hooks allowCodes cb wb gasCap = .error e := by
  unfold checkD2Core
  rw [show checkD2CoreObs hooks allowCodes cb wb gasCap = .error e from h, Except.map]

/-- **On acceptance the emitted record is the computed transition.** No side condition: the output
checker *is* the computation that produced these values. A report comparing them against the claim's
header therefore measures the computation, and acceptance is the proof that they agreed. -/
theorem accepted_observable_computed (hooks : ActionHooks) (allowCodes : Bool) (cb wb : Bytes)
    (gasCap : Option Nat) (o : Observable)
    (hacc : checkD2CoreOut hooks allowCodes cb wb gasCap = .ok o) :
    checkD2CoreObs hooks allowCodes cb wb gasCap = .ok o := hacc

end NearSpecV3
