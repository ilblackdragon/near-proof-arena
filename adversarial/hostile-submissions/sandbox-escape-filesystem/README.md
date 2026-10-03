# Hostile case: sandbox-escape-filesystem

**Attack family:** sandbox-escape

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** PROVER_RELIABILITY
**Expected reason code(s):** PROVER_FAILED

## What this proves about the judge

`prove` tries to read /etc/passwd and ~/.ssh and to write outside the scratch dir, then exits without producing a proof. The bundle is read-only, home is absent and writes outside scratch are denied, so the attempt is contained and has no effect; the observable kill is PROVER_RELIABILITY (no proof).

## Notes

HONEST OBSERVABLE on bwrap-dev (no seccomp): the escape attempt is contained and has no effect, so the kill is 'no proof produced' (PROVER_FAILED), not a dedicated SANDBOX_VIOLATION. Firecracker's forged-guest-report path maps to SANDBOX_VIOLATION; sound syscall-level attempt detection in the sandbox is a runners-core follow-up (see adversarial/README.md).
