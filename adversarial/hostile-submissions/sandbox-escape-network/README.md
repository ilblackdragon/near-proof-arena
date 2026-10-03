# Hostile case: sandbox-escape-network

**Attack family:** sandbox-escape

**Expected decision:** REJECTED
**Expected failing gate(s):** PROVER_RELIABILITY
**Expected reason code(s):** SANDBOX_VIOLATION

## What this proves about the judge

`prove` opens an outbound TCP connection. The sandbox has no network (`network: None`); any connect attempt must fail and be flagged as SANDBOX_VIOLATION.

## Notes

The escape must fail harmlessly; the submission is REJECTED and the attempt recorded. Gate attribution (PROVER_RELIABILITY / BENCHMARK) depends on which stage runs the sandboxed binary.
