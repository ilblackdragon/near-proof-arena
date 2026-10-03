# Hostile case: precomputed-fixture-table

**Attack family:** benchmark-cheat

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** CONFORMANCE_DIFFERENTIAL
**Expected reason code(s):** CLAIM_MISMATCH

## What this proves about the judge

`prepare` writes a tiny table of answers for public fixtures into the public dir; `prove` just looks the request up and returns a wrong product on a miss. `prepare` never sees the challenge inputs (they are sampled after freeze), so held-out inputs miss the table and CONFORMANCE_DIFFERENTIAL fails. Setup that depends on challenge inputs is impossible.
