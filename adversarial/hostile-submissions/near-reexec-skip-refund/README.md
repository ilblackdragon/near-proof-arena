# Hostile case: near-reexec-skip-refund

**Attack family:** theorem-type-mismatch (a weakened verifier with a genuine certificate for the wrong theorem)

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_SEMANTIC_SOUNDNESS (and the other formal gates)
**Expected reason code(s):** THEOREM_TYPE_MISMATCH

This package is a copy of the reference candidate `examples/reexec-witness`
with one sabotage: its verifier model checks a *weakened* relation.

* `formal/ReexecWitness/Model.lean`: `check` decides `WeakRelation`, which is
  `NearRelation` with `refundCount` and `refundsCommitment` dropped from the
  output comparison. The judge compiles exactly this model (native-lean
  route), so the deployed verifier really is weak. Locally, the honest proof of
  `s20261003-v0` (7 refunds) **is accepted** with a claim whose refund count
  and refunds commitment are both altered. The reference verifier rejects it.
* The prover is honest, so `CONFORMANCE_DIFFERENTIAL`, `PROVER_RELIABILITY` and
  `ADVERSARIAL_PROOFS` (927 proof mutants, all rejected) pass. Only the formal
  gate can see the bug.
* `formal/ReexecWitness/Obligations.lean` and `Certificate.lean`: the author
  cannot prove `DeterministicSound` for `NearRelation`, so they restate the
  challenge with `Rel := WeakRelation` (`weakSpec`, `weakParams`) and prove
  the full admission statement for *that*. The proof is genuine and uses only
  `propext`, `Classical.choice` and `Quot.sound`.

## What this proves about the judge

The judge, not the candidate, constructs the certificate's type
(`ArenaExpectedInst.expectedType` = `AdmissionStatement params{spec :=
challengeSpec} {.., nativeTrusted .. Model.verifier}`). A certificate about a
different relation does not have that type, so it fails with
`THEOREM_TYPE_MISMATCH` however clean its proof is. Locally (judge-local
emulation of the Expected module), `example : ArenaExpectedInst.expectedType
:= ReexecWitness.certificate` is a type error.
