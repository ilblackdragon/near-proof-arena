# Hostile case: malicious-executable

**Attack family:** artifact-binding

**Targets:** near-formal  (runnable: true)

**Expected decision:** REJECTED
**Expected failing gate(s):** ARTIFACT_BINDING
**Expected reason code(s):** ARTIFACT_BINDING_FAILED

## What this proves about the judge

formal/ is byte-identical to the reference, so the certificate is correct about ReexecWitness.Model.verifier and every FORMAL_* gate passes. The build recipe, however, compiles a BACKDOORED copy of the model (source/verifier/Model.backdoor.lean: accepts any proof whose first byte is 0xEE) into out/verify with the same Lean toolchain. Under verify_route = native-lean only the judge's own build of the certified model may run; a shipped verifier whose digest differs must fail ARTIFACT_BINDING. (Complements near-reexec-malicious-executable, which ships a Rust binary.)

## Package

Derived case: the reference `examples/reexec-witness` (see `BASE`) with only the files in this directory replaced/added; the e2e driver materializes base + overlay before packing. Every other file -- model, prover, build recipe, lemmas -- is the admitted reference.
