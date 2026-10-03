# Hostile case: sandbox-escape-network

**Attack family:** sandbox-escape

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** PROVER_RELIABILITY
**Expected reason code(s):** PROVER_FAILED

## What this proves about the judge

`prove` tries to open an outbound TCP connection, then exits without a proof. The sandbox has no network (`network: None`), so connect fails; the observable kill is PROVER_RELIABILITY.

## Notes

HONEST OBSERVABLE on bwrap-dev (no seccomp): the escape attempt is contained and has no effect, so the kill is 'no proof produced' (PROVER_FAILED), not a dedicated SANDBOX_VIOLATION. Firecracker's forged-guest-report path maps to SANDBOX_VIOLATION; sound syscall-level attempt detection in the sandbox is a runners-core follow-up (see adversarial/README.md).
