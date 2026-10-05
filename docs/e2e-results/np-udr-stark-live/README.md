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
  of 2.0 s, 6.5 s and 62 s (batch-1, batch-16, batch-256) against
  re-execution baselines of 6.2–10.2 ms (`classes.txt`). Verify takes
  0.43–0.78 s. The largest proof is 3.1 MB and peak RSS ≤ 3.5 GB.

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

## np-udr-stark-fast (prover-only child)

`sub_56bb976bc115412483197db8d34c3092` (`examples/np-udr-stark-fast`,
`--parent sub_19cc9c90…`). It was packed with `arena pack` from main's tree,
with the vendored crates (`8305b575…`) and the synced formal sources;
`formal/` is identical to the parent's. The package ships `out/prove` (AVX2)
and `out/prove-avx512`, chosen at runtime by CPU dispatch.

* **ADMITTED**, change class **PROVER_ONLY**. The six formal gates are
  `reused_from` the parent, so no FORMAL_CHECK job ran. CONFORMANCE (26/26,
  including 3 held-out), ADVERSARIAL, RESOURCE_LIMITS, PROVER_RELIABILITY
  and BENCHMARK re-ran and passed (`fast-status.json`; signed report in
  `fast-report.json`).
* **Score 0.048** (rank 5), below the parent's 0.052. Live prove medians,
  fast vs parent: batch-1 3.05 s vs 1.99 s, batch-16 9.14 s vs 6.49 s,
  batch-256 48.7 s vs 62.2 s. Verify is unchanged (0.44 / 0.58 / 0.78 s)
  and peak RSS is 1.5 GB. The BENCHMARK summary also records
  "session 1: CACHING_SUSPECTED; re-measured on fresh batches only".
  The expected speed-up (L8 measured about 7.6 s for batch-256 outside the
  judge) did not show under the judge's benchmark VM (8 vCPUs on CPUs 0-7,
  Firecracker). Whether the AVX-512 dispatch fires inside the guest has not
  been verified yet.
