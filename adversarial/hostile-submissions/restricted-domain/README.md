# Hostile case: restricted-domain

**Attack family:** theorem-type-mismatch

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_SEMANTIC_SOUNDNESS
**Expected reason code(s):** THEOREM_TYPE_MISMATCH

## What this proves about the judge

The reference proof, but the certificate carries an extra DOMAIN hypothesis `NearSpec.Params.maxBatch = 1` ("certified for single-receipt batches only"); the challenge's maxBatch is 256, so the certificate says nothing about the real domain. Its type is not the required statement -> FORMAL_SEMANTIC_SOUNDNESS fails with THEOREM_TYPE_MISMATCH.

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.
