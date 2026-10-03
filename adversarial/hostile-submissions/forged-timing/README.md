# Hostile case: forged-timing

**Attack family:** benchmark-cheat

**Expected decision:** REJECTED
**Expected failing gate(s):** BENCHMARK
**Expected reason code(s):** SANDBOX_VIOLATION

## What this proves about the judge

`prove` prints fabricated fast timings to stdout and tries to tamper with the clock (clock_settime / adjtimex) so self-reported timing looks better. The supervisor measures wall time itself and ignores stdout; clock tamper is a privileged syscall denied in the sandbox (SANDBOX_VIOLATION). The build LD_PRELOAD/faketime trick is defeated by the fixed env allowlist.

## Notes

If clock tamper is silently ignored rather than flagged, the kill still holds: supervisor-measured timing is used, so forging gains nothing. Reported gate may be BENCHMARK or PROVER_RELIABILITY.
