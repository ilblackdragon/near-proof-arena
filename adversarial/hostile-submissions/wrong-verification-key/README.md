# Hostile case: wrong-verification-key

**Attack family:** artifact-binding

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED, THEOREM_TYPE_MISMATCH

## What this proves about the judge

`prepare` deploys a public key (public.bin) for protocol version 85 instead of the approved pv-86 params, while the certificate is about the approved key (its type pins sha256:38c230e85240...). The statement pins sha256 of the public.bin the judge-run prepare actually wrote, so the certificate does not cover the deployed key: THEOREM_TYPE_MISMATCH and ARTIFACT_BINDING_FAILED.

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.
