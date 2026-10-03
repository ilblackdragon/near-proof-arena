# Hostile case: additional-axiom

**Attack family:** axiom-audit

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** AXIOM_AUDIT
**Expected reason code(s):** FORBIDDEN_AXIOM

## What this proves about the judge

The reference certificate, but verifier completeness (`check_complete`) is ASSUMED via a candidate-declared `axiom` instead of proved. The certificate still has exactly the judge's statement type, so only the axiom audit can catch it: the axiom is not on the challenge allowlist (propext, Quot.sound, Classical.choice) -> FORBIDDEN_AXIOM.

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.
