import NearSpecV3.Observable
import NearSpecV3.ChunkValidationD1

/-!
# `NearSpecV3.ChunkValidationD1Out` — the D1 transition returning its outputs

`checkD1CoreObs` (`ChunkValidationD1.lean`) runs the whole D1 chunk transition and validates every
consensus output against the endorsed header, then returns the record of values it computed. The signed
`checkD1` is definitionally its projection to the verdict
(`(checkD1CoreObs …).map fun _ => ()`), so the relation, every verdict and every downstream proof are
unchanged. This module is the reporting layer over that checker: it re-exports the observable checker
under the name the driver uses, states the projection theorems, and names D1's header comparison as a
predicate over the emitted record.

## Why D1 needed its own projection

D3's `checkD2CoreObs` and D2's `checkD2CoreOut` emit the record the pipeline computed; D1's `checkD1`
returned `Except String Unit` and threw its computed outputs away. The comparison block at
`ChunkValidationD1.lean` step 3.7 tests ~13 outputs against the endorsed header, so the values existed
but never escaped. `checkD1CoreObs` returns them; `checkD1CoreOut` is that same computation.

## What the emitted record is, and is not

Every field is a value the pipeline **computed** and then compared against the endorsed header — not a
read-back of the header:

| field | computed as | compared against |
|---|---|---|
| `stateRoot` | `root` after the main and all implicit transitions | `H.prevStateRoot` |
| `outcomeRoot` | `outcomeRootD1 out.outcomes` | `H.prevOutcomeRoot` |
| `gasBurnt` | `out.gasUsed` | `H.prevGasUsed` |
| `balanceBurnt` | `out.tokensBurnt` | `H.prevBalanceBurnt` |
| `outgoingReceiptsRoot` | `outgoingReceiptsRoot L out.outgoing` | `H.prevOutgoingReceiptsRoot` |
| `proposals` | `[]` (D1 computes no proposal list) | `H.proposals.isEmpty` |
| `txRoot` | `merklizeBorsh (w.newTxs.map Tx.raw)` | `H.txRoot` |
| `encodedMerkleRoot` | Reed–Solomon encoded body | `H.encodedMerkleRoot` |
| `encodedLength` | Reed–Solomon encoded body | `H.encodedLength` |
| `congestion` | `ownCongestion` (own slot info + allowed shard) | `H.congestion` |
| `bwRequests` | `[]` (D1 computes no bandwidth requests) | `H.bwRequests.isEmpty` |
| `logs` | `out.outcomes.map (·.logs) \|>.flatten` | folded into `outcomeRoot` |
| `receiptCount` | `out.outgoing.length` | folded into `outgoingReceiptsRoot` |
| `wasmGas` | `0` (no WASM in D1) | not compared |

The three fields D1 does not compute are recorded as what the checker actually establishes: the two
lists are empty (the comparison's whole content is "the header's list is empty", so the computed list is
honestly empty), and `wasmGas` is `0` because D1 executes no WASM. They are not fabricated observations.

## What this buys and what it does not

**Buys.** Per accepted case, the consensus outputs as data, so a report can put them beside an
independent decode of the claim. The relation is untouched: `checkD1` is the projection, so every
existing proof about `checkD1` (including `ChunkValidationD1a` and the `zk-formal` F1 closure) sees the
same verdict, and the emitted values are the computed ones.

**Does not buy.**

1. **A numeric diff on rejected cases.** A rejected case's error string names the header field that
   disagreed (`InvalidGasUsed`, `InvalidStateRoot`, …); the computed value that differed is not emitted,
   because the checker's failing path does not return a record. The driver prints `outputs: null` there,
   which is expected and counted, not a failure.
2. **A standalone extraction theorem** "acceptance implies the header's fields equal the emitted
   record's". The emitted record is `d1Outputs` applied to the comparison's operands — the same
   expressions appear in the checks and in the `return` — so the implication is true, and
   `d1Outputs_fields` proves each emitted field *is* its computed argument. What is not proved is the
   bridge from "the do-block returned `.ok o`" to "`o = d1Outputs …`": inverting the whole pipeline
   (decoders, receipt shuffles, the implicit loop) to reach the return statement is not something this
   module attempts. D2's module makes the same choice; there the emitted record is also the pipeline's
   return value. What *is* proved here: the projection is definitional (`checkD1CoreOut_agrees`), a
   rejection carries the signed error verbatim, on acceptance the emitted record is the observable
   checker's output (`checkD1_accepted_observable_computed`), and the record's fields are its computed
   arguments (`d1Outputs_fields`, `d1Outputs_not_computed`).
3. **Any widening.** `checkD1CoreOut` accepts exactly what `checkD1` accepts.

## Axioms

Every theorem here is axiom-free within `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace NearSpecV3

open NearSpec

/-! ## D1's header-agreement predicate

Step 3.7's comparison block as one predicate over the computed record and the endorsed header. Unlike
`Observable.agreesWithHeader` (D2's), D1 checks that the header's `proposals` and `bwRequests` are
*empty* rather than equal to a computed list, and compares `congestion` against the computed
`ownCongestion`. Splitting it out lets a report name the field that disagreed. -/

/-- **The D1 header agreement predicate.** Each conjunct is one `check` of the comparison block at
`ChunkValidationD1.lean` step 3.7, restricted to the fields an `Observable` carries. Two of those checks
have no `Observable` field and are therefore not represented: `H.gasLimit == slotB2.gasLimit` (the
slot's own gas limit, not a chunk output) and `H.proposedSplit.isNone` (no shard split in D1). The
`proposals`/`bwRequests` conjuncts are `isEmpty`, because D1 computes no list and instead requires the
header's to be empty; the emitted record records that computed list as `[]`. -/
def Observable.agreesWithHeaderD1 (o : Observable) (H : ChunkInner) : Bool :=
  (H.prevStateRoot == o.stateRoot) && (H.prevOutcomeRoot == o.outcomeRoot) &&
  o.proposals.isEmpty && (H.prevGasUsed == o.gasBurnt) &&
  (H.prevBalanceBurnt == o.balanceBurnt) &&
  (H.prevOutgoingReceiptsRoot == o.outgoingReceiptsRoot) && (H.congestion == o.congestion) &&
  o.bwRequests.isEmpty && (H.txRoot == o.txRoot) &&
  (H.encodedMerkleRoot == o.encodedMerkleRoot) && (H.encodedLength == o.encodedLength)

/-- A record whose fields are an endorsed header's own values satisfies D1's header-agreement predicate
by reflexivity, provided its two list fields are empty — which is exactly what D1's comparison requires
of the header. A report can use such a record as the *expected* side. -/
theorem agreesWithHeaderD1_refl (H : ChunkInner) :
    ({ stateRoot := H.prevStateRoot
       outcomeRoot := H.prevOutcomeRoot
       gasBurnt := H.prevGasUsed
       balanceBurnt := H.prevBalanceBurnt
       outgoingReceiptsRoot := H.prevOutgoingReceiptsRoot
       proposals := []
       txRoot := H.txRoot
       encodedMerkleRoot := H.encodedMerkleRoot
       encodedLength := H.encodedLength
       congestion := H.congestion
       bwRequests := []
       logs := []
       receiptCount := 0
       wasmGas := 0 } : Observable).agreesWithHeaderD1 H = true := by
  simp [Observable.agreesWithHeaderD1]

/-! ## The output-returning checker -/

/-- The output-returning checker: the signed checker's own computation, returning the record of values
it computed and compared against the endorsed header. Definitionally `checkD1CoreObs`, so the verdict is
the signed verdict and the emitted values are the computed values — not a read-back of the header. -/
def checkD1CoreOut (claimBytes witnessBytes : Bytes) : Except String Observable :=
  checkD1CoreObs claimBytes witnessBytes

theorem checkD1CoreOut_eq (cb wb : Bytes) : checkD1CoreOut cb wb = checkD1CoreObs cb wb := rfl

/-! ## The theorems that tie the two checkers together -/

/-- **Agreement is definitional.** The output checker is the signed checker's computation. -/
theorem checkD1CoreOut_agrees (cb wb : Bytes) :
    (∃ o, checkD1CoreOut cb wb = .ok o) ↔ checkD1 cb wb = .ok () :=
  checkD1CoreObs_agrees cb wb

/-- A rejection carries the signed checker's error string verbatim. -/
theorem checkD1CoreOut_reject (cb wb : Bytes) (e : String)
    (h : checkD1CoreOut cb wb = .error e) : checkD1 cb wb = .error e :=
  checkD1CoreObs_reject cb wb e h

/-- **On acceptance the emitted record is the computed transition.** No side condition: the output
checker *is* the computation that produced these values. A report comparing them against the claim's
header therefore measures the computation, and acceptance is the proof that they agreed. -/
theorem checkD1_accepted_observable_computed (cb wb : Bytes) (o : Observable)
    (hacc : checkD1CoreOut cb wb = .ok o) : checkD1CoreObs cb wb = .ok o := hacc

/-- The signed checker accepts exactly when the output checker does. -/
theorem checkD1_ok_iff_coreOut_ok (cb wb : Bytes) :
    checkD1 cb wb = .ok () ↔ ∃ o, checkD1CoreOut cb wb = .ok o :=
  (checkD1CoreOut_agrees cb wb).symm

/-- The signed checker rejects exactly when the output checker rejects. -/
theorem checkD1_error_iff_coreOut_error (cb wb : Bytes) (e : String) :
    checkD1 cb wb = .error e ↔ checkD1CoreOut cb wb = .error e := by
  unfold checkD1 checkD1CoreOut
  rw [Except.map.eq_def]
  cases checkD1CoreObs cb wb <;> simp

/-! ## Axiom audit -/

#print axioms checkD1CoreObs_agrees
#print axioms checkD1CoreObs_reject
#print axioms checkD1CoreOut_agrees
#print axioms checkD1CoreOut_reject
#print axioms checkD1_accepted_observable_computed
#print axioms checkD1_ok_iff_coreOut_ok
#print axioms checkD1_error_iff_coreOut_error
#print axioms agreesWithHeaderD1_refl
#print axioms d1Outputs_fields
#print axioms d1Outputs_not_computed

end NearSpecV3
