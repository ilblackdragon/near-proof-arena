# Lane log: workplan items 9 (W01 observables) and 10 (W05–W07 remaining shapes), 2026-10-29/30

Branch `worktree-agent-a9643a9ead88f35f6`, base `4f07a7fdf`. Item 10 ran in a forked worktree
(`worktree-agent-ad54daf2830fc99ec`) and was merged here. Evidence:
[w01-observables-v3](../evidence/lean-chunk-completion/w01-observables-v3/README.md) (item 9) and
[remaining-shapes](../evidence/lean-chunk-completion/remaining-shapes/README.md) (item 10; log
[lean-remaining-shapes-2026-10-29](lean-remaining-shapes-2026-10-29.md)).

## Timeline

1. The workplan, the full-observables evidence and the comparator were read. The existing expected
   records already held nearcore's `Failure(<Debug>)` text and per-outcome `compute_usage`. Per-change
   causes had been stripped, and the raw runs were gone.
2. Lean design choice for failure kinds. Threading a kind through `D2/Actions` /
   `Logged/D2Actions` would have changed the signed definitions and the `Logged ↔ D2` relational
   proofs. Instead, a classifier (`Successor/FailureKinds.lean`) re-evaluates the failed action's
   conditions in nearcore order on the pre-action state. It runs only after a real failure and only
   when `observeDetail` is set.
3. Per-outcome compute and per-receipt overlay diffs are recorded in the successor's `Recording`
   state and returned through `MainOutD2.detail` / `Observable.detail`.
4. Oracle: per-change detail with pre-state value references (`observables.rs`, `mainnet_obs.rs`).
   d1run and d2corpus.v2 are observed by re-running the unchanged D1/D2 chains with a judge hook
   (`d12obs.rs`, `judge_hook.rs`). Cold validator runtime; bound by hash; byte-identity required.
5. First comparisons against the committed expected sets: 132/132 yield failure kinds matched at
   once. Curve showed 27 mismatches, all of one encoding difference: the Lean VM reports some host
   errors in nearcore's Display text (`HostError(AltBn128 invalid input: …)`). The canonicalizer now
   maps those through the same Display table. This was not a semantic difference.
6. First attribution runs (yield 4242, global-cache 2718) showed 20/966 and 56/501 chunks
   mismatched. Three causes, none semantic:
   * outgoing-buffer writes are logged by nearcore under the next commit's cause (`lib.rs:963`
     commit, then `:1109` buffering). These keys are excluded from per-receipt attribution and stay
     compared chunk-wide;
   * a receipt postponed and completed in one chunk has two Lean entries, and the comparator's id map
     must route `PostponedReceipt{h}` to the first;
   * keys the step wrote without reading have no pre-state value in the witness. Lean now emits these
     as `preKnown: false`, and they must match a nearcore commit in the same entry.

   After the fixes: 966/966 and 501/501.
7. Controls: two comparator-control bugs were found and fixed (`attrib.cause` drawing unobservable
   same-value rewrites; `outcome.failureKind` mutating `Expired` into `Expired`). The affected
   populations were re-run (`fo3`).
8. Deliberate-breakage checker `lean-ctl` (B1 kinds, B2 tx compute, B3 attribution) built from a copy
   of the tree.
9. Host load (load average up to ~170, zkbuild slice at 45 of 48 GB): `D2ReceiptsAAR.lean` took ~70
   min wall for 15 min CPU. After the coordinator's request (2026-10-30 ~00:10) every batch ran with
   at most 4 concurrent processes across both lanes.

## Measured vs carried over

Everything in the evidence tables was measured on this branch's checker
(`nearspec-v3-check-successor` sha256 `eba960d0…`, built at `4f52dac49`) against nearcore records
captured in this lane, except the committed expected sets of
[full-observables](../evidence/lean-chunk-completion/full-observables/README.md). Those were
captured on 2026-10-26 and reused as is: their failure-error text and per-outcome compute are
nearcore's own, but they carry no per-change causes, so they give no attribution comparison.

## Commits

* `c3eff0592` W01: failure kinds, per-outcome compute and per-receipt storage attribution
* `9666f2391` Merge item 10 (`7f6786eb4` generators, `38b7b01be` evidence)
* `4f52dac49` W01 attribution: unknown pre-state values, outgoing-buffer bookkeeping, postponed receipts
* `1ee813345` comparator control fix; ML-DSA README stale claim superseded
* the evidence commit for this log and w01-observables-v3 (final results: 28,070 graded rows, 0 mismatches, 26,421/26,421 controls)

## Not done here, by rule

The workplan, `docs/HANDOVER.md` and `docs/research/lean-chunk-coverage.json` are untouched. Nothing
was pushed. No runner was registered and no repository variable was set.
