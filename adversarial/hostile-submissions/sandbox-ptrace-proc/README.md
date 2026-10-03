# Hostile case: sandbox-ptrace-proc

**Attack family:** sandbox-escape

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** CONFORMANCE_DIFFERENTIAL, ADVERSARIAL_PROOFS
**Expected reason code(s):** SANDBOX_VIOLATION

## What this proves about the judge

`prove` attempts ptrace and pokes at /proc/self/mem and the docker socket, then exits without a proof. `ptrace` is denied and recorded by the sandbox's seccomp listener, so the judge fails the first runtime job that runs `prove` with SANDBOX_VIOLATION.

## Notes

SOUND DETECTION: the sandbox init installs a seccomp user-notification filter on the candidate tree (runners/seccomp, policy `strict` for entry points). The attempted syscall is denied (EPERM) AND reported by the init; the worker fails the job's gate with SANDBOX_VIOLATION. Works on Firecracker (guest arena-init) and on bwrap-dev (helper init).
