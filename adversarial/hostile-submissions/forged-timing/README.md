# Hostile case: forged-timing

**Attack family:** benchmark-cheat

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** CONFORMANCE_DIFFERENTIAL, ADVERSARIAL_PROOFS
**Expected reason code(s):** SANDBOX_VIOLATION

## What this proves about the judge

`prove` prints a fabricated fast timing to stdout and tries to tamper with the clock (clock_settime), then exits without a valid proof. The supervisor measures wall time itself and ignores stdout; clock_settime is denied. The clock_settime attempt is denied and recorded by the sandbox's seccomp listener, so the judge fails the first runtime job that runs `prove` with SANDBOX_VIOLATION.

## Notes

Supervisor-measured timing is authoritative, so the fake print is futile; the clock tamper is contained (EPERM) and reported: SOUND DETECTION: the sandbox init installs a seccomp user-notification filter on the candidate tree (runners/seccomp, policy `strict` for entry points). The attempted syscall is denied (EPERM) AND reported by the init; the worker fails the job's gate with SANDBOX_VIOLATION. Works on Firecracker (guest arena-init) and on bwrap-dev (helper init).
