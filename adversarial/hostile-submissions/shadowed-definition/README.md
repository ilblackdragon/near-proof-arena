# Hostile case: shadowed-definition

**Attack family:** axiom-audit

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** SHADOWED_DEFINITION

## What this proves about the judge

The package ships its own copy of the trusted module NearSpec.TransferV1 (formal/NearSpec/TransferV1.lean) next to the reference proof. If the candidate's copy were loaded in place of the judge's, the relation the certificate is about could be silently weakened. Candidate modules inside judge-reserved namespaces are refused: SHADOWED_DEFINITION.

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.
