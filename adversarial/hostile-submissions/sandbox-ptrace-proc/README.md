# Hostile case: sandbox-ptrace-proc

**Attack family:** sandbox-escape

**Expected decision:** REJECTED
**Expected failing gate(s):** PROVER_RELIABILITY
**Expected reason code(s):** SANDBOX_VIOLATION

## What this proves about the judge

`prove` attempts ptrace and pokes at /proc/self and the docker socket to break out. All are denied/absent in the sandbox and must be reported as SANDBOX_VIOLATION.

## Notes

The escape must fail harmlessly; the submission is REJECTED and the attempt recorded. Gate attribution (PROVER_RELIABILITY / BENCHMARK) depends on which stage runs the sandboxed binary.
