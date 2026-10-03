# Hostile case: precomputed-fixture-table

**Attack family:** benchmark-cheat

**Expected decision:** REJECTED
**Expected failing gate(s):** CONFORMANCE_DIFFERENTIAL
**Expected reason code(s):** CLAIM_MISMATCH

## What this proves about the judge

The backend does the heavy work in `prepare` by precomputing answers for a table of PUBLIC fixtures, so timed `prove` looks instant. This cannot work: `prepare` receives only approved params (never the challenge inputs, which are sampled after freeze), so held-out inputs are not in the table and CONFORMANCE_DIFFERENTIAL fails.

## Notes

Demonstrates the 'omitted setup cost' invariant: setup that depends on challenge inputs is impossible because inputs post-date freeze.
