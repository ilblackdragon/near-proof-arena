# Hostile case: build-dependency-substitution

**Attack family:** build-integrity

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED

## What this proves about the judge

The recipe substitutes a different source for a locked dependency (ignores dependency-locks and compiles an alternate file). Either the build output digest diverges from the certified artifact (ARTIFACT_BINDING) or the reproducibility/lock check fails (BUILD_FAILED).

## Notes

BUILD_FAILED acceptable if lock enforcement rejects the substitution before artifact binding.
