# Older worktree reconciliation — 2026-10-23

User-authorized audit, integration and cleanup. Baseline `f49deaf7c`; carried forward concurrent
main updates before final integration. Changes were assembled in `integration/worktree-audit-20261023`.

## Recovered into main

* **`pq-chunk-perf` (five commits through `84be02c50`):** D0a chunk recursion driver, public-input
  reconstruction, setup pinning, independent verification, profiling and replay utilities, packet
  artifacts, depth-law and S=13 measurement evidence. Rebuilt the driver from the integrated source
  using the existing pinned dependency tree (`cargo build --offline --release --locked -j 8`).
  Checked all six artifact hashes plus the decompressed setup hash. The independent verifier
  accepted **299,967 bytes**; corrupted proof, trailing bytes, truncated hint and untrusted setup
  pin were each rejected. This is the measured D0a fixture, not D3 or a production aggregation tree.
  The conflicting aggregation-plan appendices were both retained, as sections 8 and 9.
* **`air-polynomial-lowering`:** recovered `RecursiveSourceCompiler`, `RecursiveSharedBranches`
  and `RecursiveSharedQueries` (three previously untracked Lean modules). Each built against
  current sources; all 27 public theorem declarations were axiom-audited, with no `sorryAx`.
  Imports added to `NearCompression.lean` so default library builds reach them. These prove
  conditional source-compilation/shared-query facts, not end-to-end cryptographic soundness.
* **`sumcheck-round-bound`:** recovered `PreparedMemoryServiceSmoke.lean`. Its dependency target
  built (313 jobs), then `lake env lean --run PreparedMemoryServiceSmoke.lean` passed: empty and
  ordered-overwrite positives plus eight chronology/root/request forgery controls.
* **`pq-cpu-prover`:** recovered the uncommitted `streamext` and `dftshare` benchmark modes.
  Rebuilt the example against the existing CPU dependency tree. Two-thread small runs passed:
  `dftshare 2 4 8 4` and `streamext 1 8 2 1 3`. These are diagnostic helpers, not new performance
  claims. The initial even odd-domain-factor smoke argument was invalid and was corrected to 3.
* **`v3-prover-walk`:** merged its remaining historical progress-log commit `a61c204c1`.
  Its old scheduler implementation was already replaced by the integrated conformance implementation.

Machine-readable source hashes, axiom output and validation scope:
`research/near-compression/results/worktree-recovery-20261023/VALIDATION.json`.
`make pin-check` and `git diff --check` pass. No new expensive proving benchmark was run.

## Retired worktrees and why

| Worktree(s) | Disposition |
|---|---|
| `judge-fc-batch`, `v3-deploy-d0a` | Clean, all commits already ancestors of main. |
| `pq-agg-rebase`, `pq-cd-render`, `pq-d3-air`, `pq-hch`, `pq-if2`, `pq-reg-hsend`, `pq-rowif`, `pq-hostfinal` | Committed work already integrated; stale tracked build-output deletions were not source changes. Open follow-ups remain in handover. |
| `pq-family-qrom`, `pq-hash-bridge`, `pq-nv-faithful`, `pq-paper-soundness`, `pq-whir-transfer` | Their checkpoints already integrated. Retiring worktrees does not close their named security/trust obligations. |
| `pq-native-hermetic` | Commits integrated. Uncommitted G2 log append repeats the measured gate and corrections already present in main; archived instead of duplicating it. |
| `novelty-prior-art` | Main already contains the reviewed, deliberately redacted prior-art document. Aborted a tentative integration on finding the restriction; did not import the older restricted text or its branch history. Restricted note already exists outside the repo. |
| `air-polynomial-lowering`, `generic-air-reference`, `sumcheck-round-bound` | Most files byte-identical to main; differing existing proof files are older versions missing main's later results. Recovered the validated additions above. Unique experimental models/tests/capture results remain in the recovery archive. |
| `direct-wasm-whir` | Branch integrated; leftover long1025 fixture/generated proof data archived. |
| `pq-cpu-prover`, `pq-chunk-e2e` | Useful changes recovered as above; checkpoint worktrees retired after integration. |
| `v3-d1-tables` | 48 generated untracked modules fail as a set. `LinkSched` has dependent-decision/rewrite errors; `RecModel` has stale interface/type errors; `A7Bound` times out at 200,000 heartbeats. All 48 depend on these failures. Archive preserves the source and build log; no default-build imports added. |
| `v3-domain-bounds` | Only a formatting-only sample edit and generated Lake manifest; superseded. |
| `v3-prover`, `v3-prover-walk` | Old scheduler dumper replaced by `Conformance/SchedJson.lean` and the current `SchedEntriesV3.lean`; documented in `v3-prover-schedqv-2026-10.md`. |
| `zk-L4-test` | Reference prover compiles, but four honest toy acceptance controls fail. Current verifier requires `minQueryLog = 8`; old toy fixtures do not meet the current domain gate. Negative tests alone do not validate an oracle. Archived, not merged. |
| `zk-L8-lean`, `zk-L8-sha` | Both `noncomputable def all` changes already in main; archived old conformance evidence. |
| `memio-head`, `prememio`, `mtest-cd` | Temporary checkouts; MEMIO commits remain in the retained active lane; CD/gas test-merge work superseded by main. Dirty test merge saved before removal. |

Three additional memory-stack modules (`PreparedMemorySenderTransition`, `PreparedMemorySenderNextStack`,
`PreparedMemoryFullStackExec`) were tested but not integrated: the first times out at its existing
4,000,000-heartbeat limit (lines 168/182), blocking its dependents. These remain recovery material,
not a claimed closed execution proof.

## Recovery and remaining workspace

Unique dirty non-build files and binary tracked patches were saved before deletion under
`/data/illia/worktree-audit-20261023/saved/`. Ignored non-build evidence (including conformance
outputs) was compressed separately there. `inventory.json`, `comparison.json`, removal manifests
and validation logs record the decisions. Git branches remain locally recoverable; the cleanup
removes expensive working copies/caches, not branch history. No restricted material was added to
this log or to the integrated source.

Retained: active `pq-host-memio`; the eight new `lean-chunk-*` worktrees; the Claude agent checkout;
and the integration worktree until its merge is complete. The MEMIO lane has live uncommitted work
and build processes, so this old-worktree cleanup does not merge or erase it. Its "merged" note
alone is not evidence of integration. Non-Git challenge/benchmark scratch directories are outside
this worktree cleanup and remain in place.
