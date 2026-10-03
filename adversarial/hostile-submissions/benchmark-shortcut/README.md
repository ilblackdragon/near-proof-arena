# Hostile case: benchmark-shortcut

**Attack family:** benchmark-cheat

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** CONFORMANCE_DIFFERENTIAL
**Expected reason code(s):** CLAIM_MISMATCH

## What this proves about the judge

The prover returns the correct product ONLY for a hard-coded 'benchmark' request and an off-by-one wrong product for everything else. Conformance samples fresh judge inputs (sampled after freeze), so CONFORMANCE_DIFFERENTIAL against the oracle fails with CLAIM_MISMATCH. A prover that only works on known inputs cannot pass differential testing.
