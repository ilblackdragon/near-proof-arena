# Hostile case: always-reject-verifier

**Attack family:** prover-reliability

**Expected decision:** REJECTED
**Expected failing gate(s):** PROVER_RELIABILITY
**Expected reason code(s):** PROVER_FAILED

## What this proves about the judge

The verifier exits 1 for every proof, including the candidate's own honest proof. PROVER_RELIABILITY must fail: the honest prover's output does not verify, so the backend cannot discharge the required workloads.
