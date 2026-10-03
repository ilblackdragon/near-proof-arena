# Final e2e runs, lane/runners-core (after merging main)

Run 2026-10-03 on the shared dev host, tree `ac3d80a` (merge of main incl. RequestPin, bench-spec-v1.1, `chl_f7eb…` v1.1). The server is a real `arena-server` (dev mode, its own Postgres database `arena_e2e_runners`). The worker is a real `arena-worker` on bwrap-dev (`ARENA_DEV_UNSAFE=1`, DEMO tier cap). Submissions go through the `arena` CLI.

## `make e2e`: PASS (`make-e2e.log`)

* demo challenge `chl_54c65fe7c73c5abcfe500681889177bc`, toy reference `sub_ff255c4cbb364849a162fe56a78f4e73`. It reached DECIDED as ADMITTED (demo tier) with every required gate PASS from real judge work, every gate DEMO_ONLY, and rank null (`e2e-demo.report.json`, `e2e-demo.leaderboard.json`).
* the formal NEAR challenge `chl_f7eb2d91bf7b363eee134b6ad9d3e011` (v1.1) is registered. The same package was submitted to it as `sub_bf1698cbdd944131b5e07f91cd4be0e4`, and the demo-capped worker never touched it (tier caps).

## `make e2e-hostile`, live: 35/35 REJECTED, 0 admitted, 0 ranked; 10/35 match expect.json; exit 1 (`e2e-hostile.log`, `hostile-demo.json`)

It was run as `tests/e2e/run.sh --hostile`, which invokes `adversarial/e2e/run.sh` (the `make e2e-hostile` script) against the same live server, using the demo challenge.

Every hostile package is REJECTED, and none is admitted or ranked. The script exits non-zero because 25 cases do not fail the gate their expect.json names:

* formal/binding cases (sorry, native_decide, axioms, stale/missing certificate, wrong VK, …) target a challenge with formal obligations. On the demo challenge their `prove` writes no `claim.bin` for the toy encoding, so they fail PROVER_RELIABILITY first. The NEAR formal cases pass on the formal challenge (see `../milestone-d/`).
* the `near-*` cases need the Lean toolchain, so their build fails on the demo worker.
* `archive-device-file` / `archive-hardlink`: the builders cannot create those entries unprivileged and nest the package under `pkg/`, giving MANIFEST_INVALID.
* `build-nonreproducible`: `$RANDOM` under `set -u` in dash fails the build (BUILD_FAILED instead of BUILD_NOT_REPRODUCIBLE).
* `sandbox-escape-*` / `sandbox-ptrace-proc`: the attempts are contained, but escape *attempts* are not detected and reported as SANDBOX_VIOLATION (known gap).

| case | decision | failed gates | reasons | expected failing gates | matches |
|---|---|---|---|---|---|
| additional-axiom | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | AXIOM_AUDIT | no |
| always-accept-verifier | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | ADVERSARIAL_PROOFS | no |
| always-reject-verifier | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | PROVER_RELIABILITY | yes |
| archive-bomb | REJECTED | PKG_WELLFORMED | ARCHIVE_UNSAFE, OBLIGATION_UNDISCHARGED | PKG_WELLFORMED | yes |
| archive-device-file | REJECTED | PKG_WELLFORMED | MANIFEST_INVALID, OBLIGATION_UNDISCHARGED | PKG_WELLFORMED | no |
| archive-hardlink | REJECTED | PKG_WELLFORMED | MANIFEST_INVALID, OBLIGATION_UNDISCHARGED | PKG_WELLFORMED | no |
| archive-symlink-escape | REJECTED | PKG_WELLFORMED | ARCHIVE_UNSAFE, OBLIGATION_UNDISCHARGED | PKG_WELLFORMED | yes |
| archive-zip-slip | REJECTED | PKG_WELLFORMED | ARCHIVE_UNSAFE, OBLIGATION_UNDISCHARGED | PKG_WELLFORMED | yes |
| background-daemon | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | PROVER_RELIABILITY | yes |
| benchmark-shortcut | REJECTED | CONFORMANCE_DIFFERENTIAL | CLAIM_MISMATCH, OBLIGATION_UNDISCHARGED | CONFORMANCE_DIFFERENTIAL | yes |
| build-dependency-substitution | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | ARTIFACT_BINDING | no |
| build-network-fetch | REJECTED | BUILD_REPRODUCIBLE | BUILD_FAILED, OBLIGATION_UNDISCHARGED | BUILD_REPRODUCIBLE | yes |
| build-nonreproducible | REJECTED | BUILD_REPRODUCIBLE | BUILD_FAILED, OBLIGATION_UNDISCHARGED | BUILD_REPRODUCIBLE | no |
| changed-security-parameters | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | FORMAL_CRYPTO_SOUNDNESS | no |
| false-premise | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | FORMAL_SEMANTIC_SOUNDNESS | no |
| forged-pass-output | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | FORMAL_SEMANTIC_SOUNDNESS | no |
| forged-timing | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | BENCHMARK | no |
| malicious-executable | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | ARTIFACT_BINDING | no |
| missing-certificate | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | FORMAL_SEMANTIC_SOUNDNESS | no |
| native-decide-certificate | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | AXIOM_AUDIT | no |
| near-reexec-malicious-executable | REJECTED | BUILD_REPRODUCIBLE | BUILD_FAILED, OBLIGATION_UNDISCHARGED | ARTIFACT_BINDING | no |
| near-reexec-skip-refund | REJECTED | BUILD_REPRODUCIBLE | BUILD_FAILED, OBLIGATION_UNDISCHARGED | FORMAL_SEMANTIC_SOUNDNESS, FORMAL_CRYPTO_SOUNDNESS | no |
| precomputed-fixture-table | REJECTED | CONFORMANCE_DIFFERENTIAL | CLAIM_MISMATCH, OBLIGATION_UNDISCHARGED | CONFORMANCE_DIFFERENTIAL | yes |
| restricted-domain | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | FORMAL_SEMANTIC_SOUNDNESS | no |
| sandbox-escape-filesystem | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | PROVER_RELIABILITY | no |
| sandbox-escape-network | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | PROVER_RELIABILITY | no |
| sandbox-fork-bomb | REJECTED | PROVER_RELIABILITY, RESOURCE_LIMITS | OBLIGATION_UNDISCHARGED, PROVER_FAILED, RESOURCE_LIMIT | RESOURCE_LIMITS | yes |
| sandbox-ptrace-proc | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | PROVER_RELIABILITY | no |
| shadowed-definition | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | AXIOM_AUDIT | no |
| sorry-certificate | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | AXIOM_AUDIT | no |
| stale-certificate | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | ARTIFACT_BINDING | no |
| ui-injection-logs | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | ADVERSARIAL_PROOFS | no |
| ui-injection-manifest | REJECTED | PKG_WELLFORMED | MANIFEST_INVALID, OBLIGATION_UNDISCHARGED | PKG_WELLFORMED | yes |
| weak-public-input-binding | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | ADVERSARIAL_PROOFS | no |
| wrong-verification-key | REJECTED | PROVER_RELIABILITY | OBLIGATION_UNDISCHARGED, PROVER_FAILED | ARTIFACT_BINDING | no |
