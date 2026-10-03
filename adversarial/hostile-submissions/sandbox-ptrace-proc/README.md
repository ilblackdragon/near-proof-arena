# Hostile case: sandbox-ptrace-proc

**Attack family:** sandbox-escape

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** PROVER_RELIABILITY
**Expected reason code(s):** PROVER_FAILED

## What this proves about the judge

`prove` attempts ptrace and pokes at /proc/self/mem and the docker socket, then exits without a proof. All are denied/absent; the observable kill is PROVER_RELIABILITY.

## Notes

HONEST OBSERVABLE on bwrap-dev (no seccomp): the escape attempt is contained and has no effect, so the kill is 'no proof produced' (PROVER_FAILED), not a dedicated SANDBOX_VIOLATION. Firecracker's forged-guest-report path maps to SANDBOX_VIOLATION; sound syscall-level attempt detection in the sandbox is a runners-core follow-up (see adversarial/README.md).
