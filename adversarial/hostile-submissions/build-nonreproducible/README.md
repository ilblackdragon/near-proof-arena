# Hostile case: build-nonreproducible

**Attack family:** build-integrity

**Targets:** demo  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** BUILD_REPRODUCIBLE
**Expected reason code(s):** BUILD_NOT_REPRODUCIBLE

## What this proves about the judge

The build mixes bytes from /dev/urandom into the compiled verifier, so two independent judge builds are not bit-identical. BUILD_REPRODUCIBLE must fail with BUILD_NOT_REPRODUCIBLE; a non-deterministic build cannot be bound to a certified artifact.
