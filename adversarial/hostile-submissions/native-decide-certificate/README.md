# Hostile case: native-decide-certificate

**Attack family:** axiom-audit

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** NATIVE_EVAL_FOUND

## What this proves about the judge

The reference certificate with its size side-condition (`honestProofBound ≤ maxProofBytes`) discharged by `native_decide` instead of kernel `decide`. native_decide trusts the compiler and emits an auxiliary `._native` axiom (Lean.ofReduceBool); the policy forbids native evaluation, so AXIOM_AUDIT must fail with NATIVE_EVAL_FOUND even though the proposition is true.

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.
