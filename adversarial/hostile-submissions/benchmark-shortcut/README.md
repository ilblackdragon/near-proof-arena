# Hostile case: benchmark-shortcut

**Attack family:** benchmark-cheat

**Expected decision:** REJECTED
**Expected failing gate(s):** CONFORMANCE_DIFFERENTIAL
**Expected reason code(s):** CLAIM_MISMATCH

## What this proves about the judge

The prover special-cases the PUBLIC benchmark fixtures (keys a lookup table by input hash) and returns a canned claim for them, but garbage for fresh / held-out inputs. Fresh inputs are sampled AFTER freeze, so CONFORMANCE_DIFFERENTIAL against the oracle on held-out inputs must fail (CLAIM_MISMATCH).

## Notes

PROVER_RELIABILITY may also fail on fresh inputs; either is a kill.
