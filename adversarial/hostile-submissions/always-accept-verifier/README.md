# Hostile case: always-accept-verifier

**Attack family:** verifier-soundness

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** ADVERSARIAL_PROOFS
**Expected reason code(s):** HOSTILE_PROOF_ACCEPTED

## What this proves about the judge

The prover is the honest toy-arith reference, so BUILD / CONFORMANCE / PROVER_RELIABILITY pass. The verifier, however, ignores its input and exits 0 for every proof. ADVERSARIAL_PROOFS feeds hostile proof bytes and must fail: a verifier that accepts everything proves nothing.
