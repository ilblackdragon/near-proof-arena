# Hostile case: sandbox-escape-filesystem

**Attack family:** sandbox-escape

**Expected decision:** REJECTED
**Expected failing gate(s):** PROVER_RELIABILITY
**Expected reason code(s):** SANDBOX_VIOLATION

## What this proves about the judge

`prove` reads /etc/passwd, ~/.ssh and writes OUTSIDE the scratch dir. The sandbox bundle is read-only, home is absent, and writes outside scratch are denied; the attempt must be reported as SANDBOX_VIOLATION, never ignored.

## Notes

The escape must fail harmlessly; the submission is REJECTED and the attempt recorded. Gate attribution (PROVER_RELIABILITY / BENCHMARK) depends on which stage runs the sandboxed binary.
