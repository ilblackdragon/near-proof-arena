# Hostile case: stale-certificate

**Attack family:** artifact-binding

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED, THEOREM_TYPE_MISMATCH

## What this proves about the judge

The verifier model gained a release tag (`Model.release := 2`), which changes the compiled verify binary, but the certificate is stated against the PREVIOUS build's binary digest (sha256:3931ac6f2c1e..., the admitted reference's verify) instead of the judge-generated statement. The proof is sound for that old artifact but not bound to the binary built now: a PACKAGING kill, reported as THEOREM_TYPE_MISMATCH on the statement and ARTIFACT_BINDING_FAILED -- never as a semantic-soundness verdict on the model.

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.

## Notes

Classified PACKAGING: the stale digest must not be reported as a semantic-soundness failure of the model.
