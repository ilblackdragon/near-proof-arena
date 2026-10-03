# Hostile case: always-accept-verifier

**Attack family:** verifier-soundness

**Expected decision:** REJECTED
**Expected failing gate(s):** ADVERSARIAL_PROOFS
**Expected reason code(s):** HOSTILE_PROOF_ACCEPTED

## What this proves about the judge

The verifier ignores its input and exits 0 for every proof. A hostile (or empty/garbage) proof is accepted, so the ADVERSARIAL_PROOFS gate must fail: a verifier that accepts everything proves nothing.
