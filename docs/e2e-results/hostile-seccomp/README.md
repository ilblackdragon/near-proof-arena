# Sound SANDBOX_VIOLATION detection — live results

Run 2026-10-03 on the shared dev host from `lane/runners-vm-2`
(`runners/seccomp`, seccomp user-notification in the sandbox inits; see
`docs/ISOLATION.md` §2 "Escape-attempt detection").

## Hostile suite, live (demo challenge, bwrap-dev worker)

`ARENA_E2E_DB=arena_e2e_seccomp tests/e2e/run.sh --hostile` →
**22/22 run cases match `expect.json`; 0 admitted; 0 ranked** (13 near-formal
cases skipped as before). Raw: `hostile-demo.json`, `hostile-demo.log`.

| case | before | now (live) |
|---|---|---|
| `sandbox-escape-network` (`socket(AF_INET)`) | PROVER_RELIABILITY / PROVER_FAILED | **SANDBOX_VIOLATION** |
| `sandbox-ptrace-proc` (`ptrace`) | PROVER_RELIABILITY / PROVER_FAILED | **SANDBOX_VIOLATION** |
| `forged-timing` (`clock_settime`) | PROVER_RELIABILITY / PROVER_FAILED | **SANDBOX_VIOLATION** |
| `sandbox-escape-filesystem` (file opens only) | PROVER_FAILED | PROVER_FAILED (not soundly detectable; see its `notes`) |
| `build-network-fetch` (curl in the build) | BUILD_FAILED | BUILD_FAILED (builds use the `tooling` policy) |

The violation fails the gate of whichever runtime job executed `prove` first;
conformance and adversarial jobs are scheduled together, so the failed gate is
`CONFORMANCE_DIFFERENTIAL` or `ADVERSARIAL_PROOFS` (both seen across two runs);
the expectations list both. The honest toy candidate in the same e2e run is
DECIDED with every required gate PASS (no violations).

## Honest backends (false-positive check)

| backend | how | result |
|---|---|---|
| `stark-plonky3` | `runners/firecracker/scripts/honest-backend-check.sh` (Firecracker): build in the pinned toolchain image under `tooling` (45 s), prepare + prove/verify on 3 public fixtures under `strict` | 0 violations, claims == expected |
| `zkvm-sp1` | same script, SP1 toolchain image, 40 GiB VM: build (261 s), prepare, prove `example-tierA` (126 s), verify | 0 violations, claim == expected |
| `reexec-witness` | `tests/e2e/milestone-d.sh` (Firecracker worker, formal tier) | reference and PROVER_ONLY child **ADMITTED**, all 13 gates PASS; NEAR hostile cases as expected. The third submission (verifier change) ended INFRA_ERROR because the `near-arena-oracle` binary borrowed from another worktree was deleted mid-run (unrelated to detection; no violation anywhere in the worker log). |
| Lean tooling | formal-checker corpus, 30 cases, bwrap-dev and Firecracker (`tooling`) | all cases as expected (150 microVM runs) |
| toy / worker suites | `cargo test -p arena-worker` (bwrap-dev), gated worker Firecracker tests (Rust+C build with the toolchain image, conformance, adversarial, benchmark) | pass |
