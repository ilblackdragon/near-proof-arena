# Hostile case: wrong-verification-key

**Attack family:** artifact-binding

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED

## What this proves about the judge

The backend ships params/verification key for a DIFFERENT protocol version (not PV86) / different program than the challenge pins. ARTIFACT_BINDING compares the built params digest against the certified one; a wrong key must fail rather than silently verify a different statement.

## Notes

THEOREM_TYPE_MISMATCH / CLAIM_MISMATCH may also surface depending on where the version divergence is first detected.
