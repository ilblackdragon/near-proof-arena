# Hostile case: background-daemon

**Attack family:** async-cheat

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** PROVER_RELIABILITY
**Expected reason code(s):** PROVER_FAILED

## What this proves about the judge

`prove` forks a background daemon and exits immediately without writing the proof; the daemon would 'finish later'. The sandbox tears down the whole process group at exit and collects outputs only then, so the proof is absent: PROVER_RELIABILITY fails.
