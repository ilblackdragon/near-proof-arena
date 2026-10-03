# Hostile case: missing-certificate

**Attack family:** formal-missing

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_SEMANTIC_SOUNDNESS
**Expected reason code(s):** CERTIFICATE_MISSING

## What this proves about the judge

candidate.toml names `ReexecWitness.certificate`, but the Lean project only defines `ReexecWitness.certificate_draft` (same honest proof). The judge must not default to PASS or search for a look-alike: FORMAL_SEMANTIC_SOUNDNESS fails with CERTIFICATE_MISSING.

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.
