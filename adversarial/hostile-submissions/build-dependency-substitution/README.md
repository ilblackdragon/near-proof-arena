# Hostile case: build-dependency-substitution

**Attack family:** build-integrity

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** ADVERSARIAL_PROOFS
**Expected reason code(s):** HOSTILE_PROOF_ACCEPTED

## What this proves about the judge

The recipe ignores the vendored verifier source and compiles an alternate, backdoored `verify_alt.c` (always-accept) as out/verify. The build is deterministic, so it reproduces; the backdoored verifier is then caught by ADVERSARIAL_PROOFS. (On the NEAR challenge the same swap is caught earlier by ARTIFACT_BINDING against the certified verifier digest.)
