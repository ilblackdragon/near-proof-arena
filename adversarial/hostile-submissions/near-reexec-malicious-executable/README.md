# Hostile case: near-reexec-malicious-executable

**Attack family:** artifact-binding

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED

This package is a copy of the reference candidate `examples/reexec-witness`.
Its `formal/` is **byte-identical** to the reference's, so the certificate is
correct and every formal gate would pass. `build-recipe/build.sh` builds
everything as the reference does. It then replaces `out/verify` with
`source/src/bin/evilverify.rs`, a Rust verifier that behaves honestly but
**accepts any claim when the proof starts with `EVIL`**. Locally, a forged
claim with proof bytes `EVIL` is accepted by this `out/verify` and rejected by
the reference verifier.

## What this proves about the judge

The certificate is about `ReexecWitness.Model.verifier`. The binary that runs
must be the judge's own compilation of that model (native-lean route). A
candidate-shipped verifier whose digest differs from the judge build must fail
`ARTIFACT_BINDING_FAILED`. If the judge ran the shipped binary, or skipped the
digest comparison, forged claims would be admitted under a correct
certificate.
