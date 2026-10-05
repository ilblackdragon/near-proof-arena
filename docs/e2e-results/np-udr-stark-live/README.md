# np-udr-stark on the live instance: ADMITTED at formal tier (2026-10-05)

The NEAR STARK backend `examples/np-udr-stark` (`np-udr-stark-v1`,
`verify_route = native-lean`) was submitted to the live arena on
**`near-transfer-receipt-v1-6`** (`chl_7c0456cb2d1a36f8601863ac206cfcc9`).
It is **ADMITTED** at formal tier, every gate PASS, with a score, and its
report is signed.

* **Submission.** `sub_19cc9c90e2184946aad17195bd02d847`, run
  `run_66a139ae2d224d7c8043d5bd7586e2c7`.
  * The package was built with `arena pack` from main's tree (the lane
    worktree merged with main 2de621c+ / L8d), with the vendored crates
    `source/vendor` and the formal sources `formal/ZkFormal`.
  * The vendored crates' digest `8305b575…` equals
    `dependency-locks/vendor-digest.txt`. `formal/ZkFormal` was produced by
    `build-recipe/sync-lean.sh`; the lock files did not change.
  * Package TreeDigest `sha256:8eefbd19…`, 3007 files, 4.2 MB `tar.zst`.
* **Gates** (`status.json`). PKG_WELLFORMED, BUILD_REPRODUCIBLE, the four
  FORMAL_* gates, AXIOM_AUDIT, ARTIFACT_BINDING, CONFORMANCE_DIFFERENTIAL,
  PROVER_RELIABILITY, RESOURCE_LIMITS, ADVERSARIAL_PROOFS and BENCHMARK all
  PASS. The judge checked the formal gates on Firecracker with the
  lean-checker image `sha256:463fdcf4…` (checker `66b014d4…`) against the
  pinned trusted tree `sha256:35fbd260…`.
* **FORMAL_IMPL_CONNECTION** (native-lean). The evidence graph records
  `artifact:verifier_binary -implements-> formal:verifier_model` as
  **trusted**: the judge compiles the binary from the model with the
  governed Lean compiler, and this edge is not kernel-checked. It also
  records `built_from tcb:lean_compiler_runtime`. ARTIFACT_BINDING pins
  the judge-built binary's digest in the statement.
* **Signed report** (`report.json`). ed25519 over JCS(report), verified
  against `config/report-signing-key.pub.hex`.
* **Board** (`leaderboard-v1-6.txt`). Rank 4, score **0.052**: prove medians
  of about 2.0 s, 65 s and more per batch class against re-execution
  baselines of about 6–10 ms (`classes.txt`). Verify takes about 0.43–0.63 s.
  The largest proof is about 3.1 MB.

## Path to admission

1. **Run 1 (REJECTED, judge-caused).** Every formal gate failed with
   `BUILD_FAILED`: "object file …/RcptRegs4.olean … does not exist". The
   cause was that the Firecracker output channel was capped at 256 MiB and
   the checker ignored the truncation. The fix (main: cap = scratch size;
   output errors are INFRA) is described in docs/LIVE.md §5d.
2. **Run 2** reused the cached result of run 1 (formal cache). The 10 cache
   entries of checker `66b014d4…` were then invalidated through the admin
   path.
3. **Run 3.** FORMAL_CHECK attempt 1 was interrupted by the worker restart
   that deployed the fix. Attempt 2 passed all six formal gates; the rest of
   the run followed and the run was ADMITTED.

## Limitation (L8d)

Sampled workload classes prove in 13–14 s at ≤ 1.5 GB. The worst-case
adversarial maximum witness proves in 1742 s (11.4 GB), above the 600 s
per-run cap. A RESOURCE_LIMITS / adversarial case at that size would time
out.
