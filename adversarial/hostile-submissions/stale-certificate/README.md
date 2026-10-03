# Hostile case: stale-certificate

**Attack family:** artifact-binding

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED

## What this proves about the judge

The formal certificate certifies a PREVIOUS verifier (its embedded formal digests / verified-surface point at an older artifact). This is a PACKAGING kill, not a semantic one: the proof may be perfectly sound for the old verifier, but it is not bound to the artifact actually built, so ARTIFACT_BINDING fails.

## Notes

Classified PACKAGING: a stale-digest failure must NOT be reported as a semantic-soundness failure.
