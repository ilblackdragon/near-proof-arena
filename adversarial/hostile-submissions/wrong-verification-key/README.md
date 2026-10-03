# Hostile case: wrong-verification-key

**Attack family:** artifact-binding

**Targets:** near-formal  (runnable: false)

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED

## What this proves about the judge

Params / verification key for a different protocol version or program than the challenge pins. ARTIFACT_BINDING compares the built params digest against the certified one; a wrong key must fail.
