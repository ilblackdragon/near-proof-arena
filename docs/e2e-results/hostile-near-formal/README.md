# Hostile suite — NEAR formal challenge, live (Firecracker)

Run 2026-10-03 via `tests/e2e/run.sh --target near-formal` on the shared dev host: real `arena-server` + a Firecracker `arena-worker` (tier cap formal, deps `/data/illia/nearproof-deps/firecracker-rc`, newest pinned toolchain image `sha256:70d2b280…`, lean-checker image `sha256:d85133a1…` with its Lean toolchain mounted read-only into builds, NEAR oracle + public fixtures, formal sandbox memory 64 GiB). Challenge: the **signed** `chl_3be93793610370275ae40f36a475f01f` (near-transfer-receipt-v1, v1-2) itself, no local successor.

## Result: 13/13 NEAR-formal cases match expect.json; 0 admitted, 0 accepted, 0 ranked

The 22 demo-targeted cases were skipped (`targets: ["demo"]`; their live run is `../hostile-final/`). Each case is the admitted reference `examples/reexec-witness` (native-lean route), honest except for exactly one attack. Roughly 2–3 minutes per submission end to end in Firecracker (validate, two reproducible builds, judge native build of the model, formal check).

| case | submission | decision | failed gates | reasons (all gates) | expected gate / reasons | match |
|---|---|---|---|---|---|---|
| additional-axiom | `sub_747aaa3cfd574868b9ef980ded7c75ec` | REJECTED | AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | FORBIDDEN_AXIOM, OBLIGATION_UNDISCHARGED | AXIOM_AUDIT / FORBIDDEN_AXIOM | yes |
| changed-security-parameters | `sub_e8cf57b8a89240a09b78a9111ad5072c` | REJECTED | ARTIFACT_BINDING, AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED, THEOREM_TYPE_MISMATCH | FORMAL_CRYPTO_SOUNDNESS / THEOREM_TYPE_MISMATCH | yes |
| false-premise | `sub_56e21f1379b24602b864fc08229563c1` | REJECTED | ARTIFACT_BINDING, AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED, THEOREM_TYPE_MISMATCH | FORMAL_SEMANTIC_SOUNDNESS / THEOREM_TYPE_MISMATCH | yes |
| malicious-executable | `sub_9ce55c5083bb4bfda8ec7ac003602911` | REJECTED | ARTIFACT_BINDING | ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED | ARTIFACT_BINDING / ARTIFACT_BINDING_FAILED | yes |
| missing-certificate | `sub_e9889d00fbec417daf5ac24a92d30d23` | REJECTED | AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | CERTIFICATE_MISSING, INFRA_ERROR, OBLIGATION_UNDISCHARGED | FORMAL_SEMANTIC_SOUNDNESS / CERTIFICATE_MISSING | yes |
| native-decide-certificate | `sub_8d8f7009aaec4073aa7b348f5160b738` | REJECTED | AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | NATIVE_EVAL_FOUND, OBLIGATION_UNDISCHARGED | AXIOM_AUDIT / NATIVE_EVAL_FOUND | yes |
| near-reexec-malicious-executable | `sub_ccebdf09a96e44de80a3b0dfe880e8a9` | REJECTED | ARTIFACT_BINDING | ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED | ARTIFACT_BINDING / ARTIFACT_BINDING_FAILED | yes |
| near-reexec-skip-refund | `sub_795f9108981646f5a32bfc0f0a89f768` | REJECTED | ARTIFACT_BINDING, AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED, THEOREM_TYPE_MISMATCH | FORMAL_SEMANTIC_SOUNDNESS, FORMAL_CRYPTO_SOUNDNESS / THEOREM_TYPE_MISMATCH | yes |
| restricted-domain | `sub_e05b4066e84146239de6406e82d853cb` | REJECTED | ARTIFACT_BINDING, AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED, THEOREM_TYPE_MISMATCH | FORMAL_SEMANTIC_SOUNDNESS / THEOREM_TYPE_MISMATCH | yes |
| shadowed-definition | `sub_4c938931d04341f69a6f739dc9a18066` | REJECTED | ARTIFACT_BINDING, AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED, SHADOWED_DEFINITION | AXIOM_AUDIT / SHADOWED_DEFINITION | yes |
| sorry-certificate | `sub_3f92d2dec3d440fa86753a639c6ee2a6` | REJECTED | AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | OBLIGATION_UNDISCHARGED, SORRY_FOUND | AXIOM_AUDIT / SORRY_FOUND | yes |
| stale-certificate | `sub_8d679fd3c4494f44bc653f31d9200b85` | REJECTED | ARTIFACT_BINDING, AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED, THEOREM_TYPE_MISMATCH | ARTIFACT_BINDING / ARTIFACT_BINDING_FAILED, THEOREM_TYPE_MISMATCH | yes |
| wrong-verification-key | `sub_8d331dd89092409e81ea9f880629cfcf` | REJECTED | ARTIFACT_BINDING, AXIOM_AUDIT, FORMAL_CRYPTO_SOUNDNESS, FORMAL_IMPL_CONNECTION, FORMAL_SEMANTIC_COMPLETENESS, FORMAL_SEMANTIC_SOUNDNESS | ARTIFACT_BINDING_FAILED, OBLIGATION_UNDISCHARGED, THEOREM_TYPE_MISMATCH | ARTIFACT_BINDING / ARTIFACT_BINDING_FAILED, THEOREM_TYPE_MISMATCH | yes |

### Reading the gates

* On the native-lean route the formal checker attributes every finding to **all** formal gates (`conjunct_gates` unset; the admission statement is an existential, not a `∧` chain), so for example a `sorry` fails FORMAL_SEMANTIC_SOUNDNESS through AXIOM_AUDIT together. Each case's expect.json names the gate its attack is *about*; the match requires that gate to FAIL and the attack's specific reason code to be present.
* A THEOREM_TYPE_MISMATCH also fails ARTIFACT_BINDING (the worker: "certificate does not prove the statement about the built artifacts"). Axiom-audit failures leave ARTIFACT_BINDING undetermined, not failed.
* `malicious-executable` and `near-reexec-malicious-executable`: formal/ is the reference, every FORMAL_* gate PASSES, and only ARTIFACT_BINDING fails. The shipped `out/verify` (a backdoored Lean model compiled with the same toolchain, or a Rust binary, respectively) is not the judge's build of the certified model.
* `stale-certificate` is the stale-digest **packaging** kill: the certificate is pinned to the previous verifier build's digest (`sha256:3931ac6f…`, the admitted reference's verify in `../milestone-d-v1-2/`) while the model gained a release tag. It is reported as a statement mismatch plus ARTIFACT_BINDING_FAILED, never as a semantic verdict on the model.
* `changed-security-parameters` expects THEOREM_TYPE_MISMATCH (on FORMAL_CRYPTO_SOUNDNESS), not SECURITY_BOUND_INSUFFICIENT: the profile is part of the judge-built statement, so a certificate at a 40-bit target is a different theorem. The checker never emits SECURITY_BOUND_INSUFFICIENT on this route.

### Pre-validation

Every formal variant was first run through the same checker locally (`formal-check --challenge-config … --native-model …` on bwrap-dev, about 25 s each) on the exact materialized package (`adversarial/e2e/run_hostile.py --materialize DIR`); the live verdicts match those local runs.

Raw: `hostile-near-formal.json` (per case: observed vs expected), `run.log` (harness and driver transcript from the Firecracker worker onward, including the NEAR no-certificate smoke submission).
