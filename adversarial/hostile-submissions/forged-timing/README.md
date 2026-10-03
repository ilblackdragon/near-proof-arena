# Hostile case: forged-timing

**Attack family:** benchmark-cheat

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** PROVER_RELIABILITY
**Expected reason code(s):** PROVER_FAILED

## What this proves about the judge

`prove` prints a fabricated fast timing to stdout and tries to tamper with the clock (clock_settime), then exits without a valid proof. The supervisor measures wall time itself and ignores stdout; clock_settime is denied. Because forging gains nothing, the only way this changes the outcome is by breaking the prover -- observable as PROVER_RELIABILITY.

## Notes

Supervisor-measured timing is authoritative, so the fake print is futile; clock tamper is contained. The runnable kill on the demo worker is the absent proof.
