# Hostile case: false-premise

**Attack family:** theorem-type-mismatch

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** FORMAL_SEMANTIC_SOUNDNESS
**Expected reason code(s):** THEOREM_TYPE_MISMATCH

## What this proves about the judge

The certificate is `(h : False) -> <statement>`, closed by `h.elim`: trivially provable and vacuous. Model, prover and every lemma are the reference. The judge compares the certificate's type SYNTACTICALLY with the judge-constructed statement; the extra unsatisfiable premise makes it a different type -> FORMAL_SEMANTIC_SOUNDNESS fails with THEOREM_TYPE_MISMATCH (and ARTIFACT_BINDING, since the certificate no longer speaks about the built artifacts).

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.
