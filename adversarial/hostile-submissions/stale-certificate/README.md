# Hostile case: stale-certificate

**Attack family:** artifact-binding

**Targets:** near-formal  (runnable: false)

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED

## What this proves about the judge

The certificate certifies a PREVIOUS verifier (embedded formal digests point at an older artifact). PACKAGING kill, not semantic: the proof may be sound for the old verifier but is not bound to the artifact built now, so ARTIFACT_BINDING fails.

## Notes

Classified PACKAGING: a stale-digest failure must NOT be reported as a semantic-soundness failure.
