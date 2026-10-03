# Hostile case: sorry-certificate

**Attack family:** axiom-audit

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** SORRY_FOUND

## What this proves about the judge

The reference reexec-witness certificate with ONE lemma (`honest_length`, the honest-proof size bound used by verifier completeness) closed by `sorry`. Everything else -- model, prover, build, the other lemmas -- is the admitted reference. `sorry` elaborates (with a warning) to the unsound axiom `sorryAx`; AXIOM_AUDIT walks the certificate's transitive axiom closure and must fail with SORRY_FOUND.

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.
