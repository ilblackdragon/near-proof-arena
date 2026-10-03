# Hostile case: forged-pass-output

**Attack family:** forged-output

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** ADVERSARIAL_PROOFS
**Expected reason code(s):** HOSTILE_PROOF_ACCEPTED

## What this proves about the judge

The build script prints PASS and writes fake gate-result JSON files into out/; the verifier prints a PASS banner. The judge computes gates itself from measured outcomes and ignores candidate stdout and candidate-written files, so the verifier is still exercised and -- being always-accept -- fails ADVERSARIAL_PROOFS. Forged output changes nothing.

## Notes

Demonstrates judge-computed gates override forged candidate output.
