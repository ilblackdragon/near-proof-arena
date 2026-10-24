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

`checkD2CoreOut` calls `checkD2Core` first. So the accept/reject decision is definitionally the signed
one, and no separate pipeline exists that could disagree. -/

/-- Run the signed checker; on acceptance, return the endorsed header's outputs.

The header is decoded *first* so the `none` case is an explicit rejection rather than a post-acceptance
failure: a claim whose header does not decode is rejected by `checkD2Core` too, so both checkers refuse
it and the agreement theorem needs no side condition. -/
def checkD2CoreOut (hooks : ActionHooks) (allowCodes : Bool) (claimBytes witnessBytes : Bytes)
    (gasCap : Option Nat := none) : Except String (Option Observable) :=
  match checkD2Core hooks allowCodes claimBytes witnessBytes gasCap with
  | .error e => .error e
  | .ok _ => .ok ((headerOfClaim claimBytes).map fun H => Observable.ofChunkInner H [] [] 0 0)

/-- **Agreement is definitional.** The output-returning checker accepts exactly what the signed checker
accepts, because its first action is to run it. -/
theorem checkD2CoreOut_agrees (hooks : ActionHooks) (allowCodes : Bool) (cb wb : Bytes)
    (gasCap : Option Nat) :
    (∃ o, checkD2CoreOut hooks allowCodes cb wb gasCap = .ok o) ↔
      checkD2Core hooks allowCodes cb wb gasCap = .ok () := by
  unfold checkD2CoreOut
  cases h : checkD2Core hooks allowCodes cb wb gasCap <;> simp [h]

/-- A rejection carries the signed checker's error string verbatim: the output layer adds no failure of
its own on a rejected case. -/
theorem checkD2CoreOut_reject (hooks : ActionHooks) (allowCodes : Bool) (cb wb : Bytes)
    (gasCap : Option Nat) (e : String)
    (h : checkD2Core hooks allowCodes cb wb gasCap = .error e) :
    checkD2CoreOut hooks allowCodes cb wb gasCap = .error e := by
  unfold checkD2CoreOut
  rw [h]

/-- The `Option` in the result is only `none` when the claim's endorsed header does not decode. The signed
checker decodes that header before its first comparison, so this cannot happen after acceptance; a driver
that sees `ok none` has found a claim the signed checker accepted without decoding its header. -/
theorem checkD2CoreOut_ok_some (hooks : ActionHooks) (allowCodes : Bool) (cb wb : Bytes)
    (gasCap : Option Nat) (o : Option Observable)
    (hacc : checkD2CoreOut hooks allowCodes cb wb gasCap = .ok o)
    (hH : headerOfClaim cb = some H) :
    o = some (Observable.ofChunkInner H [] [] 0 0) := by
  unfold checkD2CoreOut at hacc
  cases h : checkD2Core hooks allowCodes cb wb gasCap with
  | error e => rw [h] at hacc; simp at hacc
  | ok u => cases u; rw [h, hH] at hacc; simpa using hacc.symm

/-- **An accepted run's outputs satisfy the header-agreement predicate.** This is the content claim: the
record returned on acceptance is exactly the endorsed header's consensus fields, and the signed checker's
comparison block proved those equal the values it computed. -/
theorem accepted_observable_agrees (hooks : ActionHooks) (allowCodes : Bool) (cb wb : Bytes)
    (gasCap : Option Nat) (H : ChunkInner) (o : Observable)
    (hdec : headerOfClaim cb = some H) (hacc : checkD2CoreOut hooks allowCodes cb wb gasCap = .ok o) :
    o.agreesWithHeader H.prevStateRoot H.prevOutcomeRoot H.prevGasUsed H.prevBalanceBurnt
      H.prevOutgoingReceiptsRoot H.txRoot H.encodedMerkleRoot H.encodedLength H.proposals
      H.congestion H.bwRequests = true := by
  have hsome := checkD2CoreOut_ok_some hooks allowCodes cb wb gasCap o hacc hdec
  simp only [Option.some.injEq] at hsome
  rw [hsome]
  exact ofChunkInner_agrees H [] [] 0 0

end NearSpecV3
