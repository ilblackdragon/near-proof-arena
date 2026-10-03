# Hostile case: sandbox-fork-bomb

**Attack family:** sandbox-escape

**Expected decision:** REJECTED
**Expected failing gate(s):** RESOURCE_LIMITS
**Expected reason code(s):** RESOURCE_LIMIT

## What this proves about the judge

`prove` spawns processes without bound. The sandbox pid cap and memory limits must contain it, surfacing RESOURCE_LIMIT / SANDBOX_VIOLATION rather than hanging the host.

## Notes

The escape must fail harmlessly; the submission is REJECTED and the attempt recorded. Gate attribution (PROVER_RELIABILITY / BENCHMARK) depends on which stage runs the sandboxed binary.
