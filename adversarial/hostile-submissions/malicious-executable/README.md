# Hostile case: malicious-executable

**Attack family:** artifact-binding

**Targets:** near-formal  (runnable: false)

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED

## What this proves about the judge

Correct certificate about a faithful model, but the built verifier binary differs from the certified verifier artifact. ARTIFACT_BINDING ties the running binary's digest to the formally connected artifact; a mismatch must fail. Executable analogue: near-reexec-malicious-executable.
