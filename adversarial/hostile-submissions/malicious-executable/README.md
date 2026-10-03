# Hostile case: malicious-executable

**Attack family:** artifact-binding

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED

## What this proves about the judge

The Lean certificate is correct and about a faithful model, but the built verifier binary does not correspond to the certified verifier artifact (it embeds extra accept paths). ARTIFACT_BINDING ties the running binary's digest to the formally connected artifact; a mismatch must fail.

## Notes

FORMAL_IMPL_CONNECTION may also fail; either gate failing is a valid kill.
