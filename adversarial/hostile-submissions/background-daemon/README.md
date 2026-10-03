# Hostile case: background-daemon

**Attack family:** async-cheat

**Expected decision:** REJECTED
**Expected failing gate(s):** PROVER_RELIABILITY
**Expected reason code(s):** PROVER_FAILED

## What this proves about the judge

`prove` forks a background daemon and exits immediately; the daemon keeps working and tries to write the real proof AFTER the measured call returns. The sandbox tears down the whole process group at exit and captures outputs only then, so the proof is absent/incomplete: PROVER_RELIABILITY fails and a lingering process is a SANDBOX_VIOLATION.

## Notes

SANDBOX_VIOLATION is an acceptable additional reason code (lingering process / escaped work).
