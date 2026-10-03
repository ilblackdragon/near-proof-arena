# Hostile case: weak-public-input-binding

**Attack family:** public-input-binding

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** ADVERSARIAL_PROOFS
**Expected reason code(s):** HOSTILE_PROOF_ACCEPTED

## What this proves about the judge

The prover is honest, so the honest-proof checks pass. The verifier only checks the proof's magic tag -- it does NOT recompute the checksum or bind the proof to the claim's public inputs. ADVERSARIAL_PROOFS feeds mutated proofs that keep the magic; any acceptance is HOSTILE_PROOF_ACCEPTED: a verifier that does not actually check the argument (or its binding to the claim) is unsound.
