# Hostile suite — live e2e (final)

Run 2026-10-03T08:00:56+00:00 via `tests/e2e/run.sh --hostile` against a real `arena-server` + `arena-worker` (bwrap-dev, DEMO tier) on the signed demo challenge `chl_54c65fe7c73c5abcfe500681889177bc`. Supersedes `docs/e2e-results/final-20261003/` (10/35 matched).

## Result: 22/22 run cases match expect.json; 0 admitted; 0 ranked; 13 skipped (NEAR-formal)

Every hostile submission is REJECTED, none is admitted/accepted/ranked, and the two `ui-log-injection` cases came back with no raw control characters.

The suite is now **challenge-targeted** (`expect.json` `targets` + `runnable`): a gate only exists where the challenge requires it, so formal/artifact/crypto cases carry `targets:["near-formal"]` and the demo run skips them. The demo run covers the 22 cases whose attacked gate is in the demo challenge's required obligations (PKG_WELLFORMED, BUILD_REPRODUCIBLE, CONFORMANCE_DIFFERENTIAL, ADVERSARIAL_PROOFS, PROVER_RELIABILITY, RESOURCE_LIMITS, BENCHMARK). Each demo case is the honest toy-arith reference candidate with exactly one attacked behaviour, so the attacked gate is the FIRST to fail.

## Demo run (live, target=demo)

| case | decision | failed gate | expected gate | matched reasons | match |
|---|---|---|---|---|---|
| always-accept-verifier | REJECTED | ADVERSARIAL_PROOFS | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED | yes |
| always-reject-verifier | REJECTED | PROVER_RELIABILITY | PROVER_RELIABILITY | PROVER_FAILED | yes |
| archive-bomb | REJECTED | PKG_WELLFORMED | PKG_WELLFORMED | ARCHIVE_UNSAFE | yes |
| archive-device-file | REJECTED | PKG_WELLFORMED | PKG_WELLFORMED | ARCHIVE_UNSAFE | yes |
| archive-hardlink | REJECTED | PKG_WELLFORMED | PKG_WELLFORMED | ARCHIVE_UNSAFE | yes |
| archive-symlink-escape | REJECTED | PKG_WELLFORMED | PKG_WELLFORMED | ARCHIVE_UNSAFE | yes |
| archive-zip-slip | REJECTED | PKG_WELLFORMED | PKG_WELLFORMED | ARCHIVE_UNSAFE | yes |
| background-daemon | REJECTED | PROVER_RELIABILITY | PROVER_RELIABILITY | PROVER_FAILED | yes |
| benchmark-shortcut | REJECTED | CONFORMANCE_DIFFERENTIAL | CONFORMANCE_DIFFERENTIAL | CLAIM_MISMATCH | yes |
| build-dependency-substitution | REJECTED | ADVERSARIAL_PROOFS | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED | yes |
| build-network-fetch | REJECTED | BUILD_REPRODUCIBLE | BUILD_REPRODUCIBLE | BUILD_FAILED | yes |
| build-nonreproducible | REJECTED | BUILD_REPRODUCIBLE | BUILD_REPRODUCIBLE | BUILD_NOT_REPRODUCIBLE | yes |
| forged-pass-output | REJECTED | ADVERSARIAL_PROOFS | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED | yes |
| forged-timing | REJECTED | PROVER_RELIABILITY | PROVER_RELIABILITY | PROVER_FAILED | yes |
| precomputed-fixture-table | REJECTED | CONFORMANCE_DIFFERENTIAL | CONFORMANCE_DIFFERENTIAL | CLAIM_MISMATCH | yes |
| sandbox-escape-filesystem | REJECTED | PROVER_RELIABILITY | PROVER_RELIABILITY | PROVER_FAILED | yes |
| sandbox-escape-network | REJECTED | PROVER_RELIABILITY | PROVER_RELIABILITY | PROVER_FAILED | yes |
| sandbox-fork-bomb | REJECTED | PROVER_RELIABILITY, RESOURCE_LIMITS | RESOURCE_LIMITS | RESOURCE_LIMIT | yes |
| sandbox-ptrace-proc | REJECTED | PROVER_RELIABILITY | PROVER_RELIABILITY | PROVER_FAILED | yes |
| ui-injection-logs | REJECTED | ADVERSARIAL_PROOFS | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED | yes |
| ui-injection-manifest | REJECTED | PKG_WELLFORMED | PKG_WELLFORMED | MANIFEST_INVALID | yes |
| weak-public-input-binding | REJECTED | ADVERSARIAL_PROOFS | ADVERSARIAL_PROOFS | HOSTILE_PROOF_ACCEPTED | yes |

## Skipped on the demo run (target=near-formal)

`additional-axiom`, `changed-security-parameters`, `false-premise`, `malicious-executable`, `missing-certificate`, `native-decide-certificate`, `near-reexec-malicious-executable`, `near-reexec-skip-refund`, `restricted-domain`, `shadowed-definition`, `sorry-certificate`, `stale-certificate`, `wrong-verification-key`

* `near-reexec-malicious-executable` (ARTIFACT_BINDING) and `near-reexec-skip-refund` (FORMAL_*): the executable NEAR-formal kills, full reexec-witness-derived packages, verified on Firecracker in `docs/e2e-results/milestone-d/` (run via `tests/e2e/milestone-d.sh`, or `run.sh --target near-formal`). `runnable:true`.
* the 11 generic Lean-certificate stubs (`additional-axiom`, `sorry-certificate`, `native-decide-certificate`, `shadowed-definition`, `stale-certificate`, `missing-certificate`, `false-premise`, `restricted-domain`, `changed-security-parameters`, `wrong-verification-key`, `malicious-executable`): `runnable:false`. They document the attack and its expected gate/reason, but cannot execute without a real reexec-witness backend to build; the driver skips them with that note rather than faking a run. Turning each into a reexec-witness variant (like `near-reexec-*`) is tracked follow-up.

## Documented expectation changes (vs the original suite)

Per the integration diagnosis, and never faking an outcome:

* **sandbox-escape-filesystem / -network / -ptrace-proc, forged-timing** — revised to the HONEST OBSERVABLE on bwrap-dev. bwrap-dev has no seccomp filter (it is DEMO-only for exactly this reason), so a sound `SANDBOX_VIOLATION` from a syscall-level attempt is not available. The escape/tamper attempts are contained and have no effect, and each prover then produces no valid proof, so the observable kill is `PROVER_RELIABILITY` / `PROVER_FAILED`. Firecracker's forged-guest-report path (`InfraError::GuestProtocol`) already maps to `SANDBOX_VIOLATION`; adding sound attempt-detection in the sandbox/worker is a runners-core follow-up.
* **build-dependency-substitution** — on the demo challenge there is no `ARTIFACT_BINDING` obligation, so swapping in a backdoored (always-accept) verifier is caught one gate later by `ADVERSARIAL_PROOFS`. On the NEAR challenge the same swap is caught at `ARTIFACT_BINDING` against the certified verifier digest (see `near-reexec-malicious-executable`).
* **forged-pass-output** — reframed to the demo challenge: the prover is honest, the verifier is always-accept and the build forges gate-result JSON + a PASS banner; the judge ignores candidate output and still fails `ADVERSARIAL_PROOFS`, proving the forged files change nothing.

## Fixes applied

* All demo cases rebuilt on the honest toy-arith reference so the intended gate fails first (previously 25 hit `PROVER_RELIABILITY` because their prover wrote no claim for any encoding).
* `archive-device-file` / `archive-hardlink`: `make-archive.py` writes the device / hardlink entries with Python `tarfile` (no privilege needed) and the package is no longer nested under `pkg/` (previously `MANIFEST_INVALID`).
* `build-nonreproducible`: uses `/dev/urandom` instead of `$RANDOM` (which is empty under dash + `set -u`, previously `BUILD_FAILED`), so the build succeeds non-deterministically → `BUILD_NOT_REPRODUCIBLE`.

Raw: `hostile-demo.json` (per-case observed vs expected), `hostile-demo.log` (driver transcript).
