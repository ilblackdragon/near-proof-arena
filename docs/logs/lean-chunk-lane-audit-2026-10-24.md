# Lean chunk lane audit and completion assessment

Date: 2026-10-24. Main baseline: `0f2b32171`. Assessment target:
[completion workplan W00–W16](../requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md).

This inspection covers all nine `lane/lean-chunk-L0` through `L8` branches, their local worktrees,
unique commits, merged source, lane evidence and targeted checks. It updates the earlier assessment:
W00 interfaces, W01 harness repairs and BLS host implementations are now merged. BN128 and additional
L4 resolution work remain on branches. No implementation was merged by this audit.

## Completion assessment

**We have progressed from separate prototypes toward shared integration, but are not at release
validation.** W00 has delivered the shared contracts and initial adapters. W01 has repaired the CI
corpus prerequisite and the previously unasserted exclusions. Most curve arithmetic now exists on
main or in a committed lane. However, the new crypto and global-action semantics still do not execute
through the accepted chunk path. Several required semantics have not been implemented, and the final
representative replay and admission remain open.

The main inventory is **222 rows: 147 implemented, 36 validated, 10 missing, 18 partial,
11 impossible-at-boundary**. Since the workplan baseline, nine BLS rows moved from missing to partial.
The combined missing/partial count remains **28**; the validated count is unchanged. These are
heterogeneous inventory rows, not percentages of work or proof coverage.

**Gate A: open. Gate B: open. Gate C: blocked on full semantics/validation and successor admission.**
No evidence supports a completion-time estimate or an effort percentage. Interface scaffolding,
implemented host arithmetic, whole-chunk reachability and frozen-release validation are different
milestones and must stay separate.

## Exact lane snapshots

All tips below were inspected by ancestry against the main baseline, not inferred from merge titles.
Zero unique commits means the lane's committed work is contained in main; it does not mean that lane
has completed its assigned semantics. Most lane tips predate current main and need reconciliation.

| Lane | Tip | Unique commits vs main | Current result | Next completion obligation |
|---|---|---:|---|---|
| L0 | `190841d3d` | 0 | W00's seven interfaces, aggregator and boundary owner map merged via `f4b9b4837`; `565d1b9ca` adds the successor to default targets | Reconcile open UQs and stale interface metadata; own the adapters that connect runtime dispatch to the contracts |
| L1 | `46ddb8746` | 0 | Protocol-gas successor and earlier band evidence are on main; no new fuel/termination work found | W02 fuel/capacity audit, overlap/tier proofs, protocol-limit cases |
| L2 | `46ddb8746` | 0 | Float semantics and earlier differential evidence are on main; no new runtime-error fix or generated chunk corpus found | W03 LoadingError parity; W04 varied whole-chunk float coverage |
| L3 | `b634a6c5c` | 6 | Nine BLS hosts merged; branch adds BLS provenance/test follow-ups plus three BN128 hosts and oracle/fixtures | Repair the two reproduced branch test problems, preserve main's fixture checks, review/integrate BN128; then wire accepted chunk dispatch and complete key families |
| L4 | `06dffaac6` | 6 | Additional resolving hook, `checkD3Global`, blocker proofs and evidence remain unmerged | Reconcile against W00 action/resolution APIs; implement successor action and ETH handling and positive global fixtures |
| L5 | `6bf80d533` | 0 | Storage-bound analysis/proofs only; no new recorder implementation found | W09 real accounting, per-receipt limits, chunk defer behaviour and rollback |
| L6 | `ecd5a4fbd` | 0 | Corrected genesis implementation and resharding exclusion analysis merged | W10 overlap proof/transaction-flag tests; W11 actual resharding and mixed-epoch boundaries |
| L7 | `1edbf9cb4` | 0 | W01 comparison accounting, split manifest CI and four driver builds/smokes merged via `be3ebbca8` | Observable comparison and package identity in reports; actual provisioned corpus CI; combined successor/real-window replay |
| L8 | `46ddb8746` | 0 | No new admission audit checkpoint found | W15 exact-reference signed live admission audit; W16 successor packaging/release after Gate B |

No uncommitted semantic/document edits were found in these lane worktrees during the snapshot.
L3 has an untracked `spec/lean/v3/TmpTest/` scratch directory. Generated Rust target artifacts were
excluded from that summary; their presence/deletion is not semantic progress. L3 was recently
committing; the table is a snapshot, not a claim about whether an agent is currently running.

## What W00 now supplies

The [L0 log](lean-chunk-L0-2026-10-24.md) and
[owner map](../research/lean-chunk-w00-owner-map.md) cover the seven contracts:
configuration/tiers, host dispatch, actions/receipts, resolution, trie recorder, boundary facts and
differential results. The default target now builds `NearSpecV3.Successor`; the log's original
"not reached by default build" concern is superseded by the integration fix.

`Successor/Config.lean` includes `checkSuccessor` and `checkD3GProtoFloat`, composing genesis,
floats and protocol gas. This is more than the prior three entirely separate adapters. It is still
a configuration dispatcher over existing cores, without recorded differential evidence for that
combined configuration or the final inclusion/refinement proofs.

The implementation integration gap is directly visible in source:

- `Successor.HostDispatch.successorTable` falls through to `cryptoHostCall`.
- `Wasm.Exec.callHost` still calls `hostCall`; the chunk configuration still uses `D3.d3Hooks`.
- `Successor.ActionsReceipts.pActV` represents/decodes new tags, but the chunk core still consumes
  the old D2 decoder and action path.
- Recorder and boundary interfaces expose contracts and obligations; they are not completed protocol
  storage or resharding implementations.

Remaining W00 reconciliation includes the owner map's all-17-open UQ register versus individual lane
claims of answers, stale `unimplementedHosts` descriptions after BLS additions, and the treatment of
claim/witness size restrictions. A declared `removedBy` owner or field-kind theorem is not evidence
that a semantic exclusion has actually been removed or an external fact authenticated.

## L3 implementation and integration readiness

### Merged BLS progress

Main contains BLS12-381 field/tower/pairing implementations and all nine additive host arms. The
integration also repaired three important verification problems:

- `675b3f7cf` committed 45 previously untracked fixture files: 94 directed plus 9,360 generated rows.
- `a7b691624` makes the fixture runner reject missing directories or zero input rows instead of
  accepting `0/0 ok`.
- `23d811483` regenerated coverage and moved the nine BLS rows to partial. The successor crypto table
  now has eleven implemented host arms including ecrecover and p256; the ordinary chunk table still
  does not route those calls there.

The existing integration notes record 9,454/9,454 fixture comparisons and 135/135 main-snapshot host
checks. This audit did not repeat the full pairing fixture suite. The remaining lane commits include
`oracle/bls-oracle/`, citation corrections, twelve additional dispatch assertions and the detailed
BLS handoff log; they should not be discarded just because some fixture contents were separately
integrated on main.

### Unmerged BN128 checkpoint

`f9159a590` adds the pinned zeropool-bn oracle and 56 directed plus 3,120 generated fixture rows.
`b634a6c5c` adds field/tower/group arithmetic, reduced Tate pairing, little-endian codecs, three host
arms and a fixture runner. Its commit records **56/56 directed passes**, including nearcore's 19
vectors and pairing identities. Generation of 3,120 expected rows is not evidence that all of those
rows have passed Lean; no completed generated-run result was established in this inspection.

### Reproduced branch blockers

Commands were run in `lean-chunk-L3/spec/lean/v3`, using the lane's existing compiled imports and
freshly interpreting the named test source; this was not a clean library rebuild.

```text
lake env lean --run TestBLS12381Host.lean
BLS HOST FAIL: dispatch: alt_bn128 not claimed by this table
bls12381 host cases: 147 total, 1 failures
exit 1

lake env lean --run TestAltBn128.lean /tmp/nearproof-inspection-missing-fixtures
missing fixture dir: /tmp/nearproof-inspection-missing-fixtures
alt_bn128 fixtures: 0/0 ok, 0 failures
exit 0
```

The first is a stale negative dispatch assertion: BN128 is now intentionally present. Update that
expectation while preserving unknown-name negatives and positive dispatch tests. The second is the
same vacuous-evidence problem already fixed for BLS on main; make missing/empty BN128 evidence fail.
Then rebuild and rerun both suites on the reconciled tree. The lane also predates main's BLS runner
repair; preserve `a7b691624` when reconciling, rather than copying the lane's older runner over it.

Additional integration requirements: restore oracle reproducibility inputs missing from main,
reconcile the generated inventory, validate generated BN128 vectors/host charge order and finally
exercise all host families through valid/invalid whole chunks. No curve-host completion is certified
by arithmetic fixtures alone. secp256k1 transaction/delegate verification and ML-DSA remain separate
W06 work, not completed by recovery or pairing implementations.

## L4 integration readiness

The six branch-only commits add `GlobalContractCall.lean`, `GlobalContractChunk.lean`, two drivers,
proofs of the ETH guard limitation, a log and evidence. The recorded scoped replay is **539/539
identical verdicts and reasons**, plus **300/300** existing accepted cases still accepted. This is
preservation evidence, not new end-to-end acceptance: no account in the scoped fixtures exercises
global/by-account resolution or the wallet redirect.

Three remaining implementation dependencies are concrete:

1. Consume W00's widened action representation/decoding in a successor chunk path; the old D2
   decoder rejects tags 9/10/11 before their action bodies execute.
2. Implement successor ETH guard behaviour. The resolution wrapper yields `.local` and therefore
   still triggers the old blanket ETH-local exclusion. Preserve signed behaviour, but do not mistake
   the need for a shared adapter edit for a protocol impossibility.
3. Generate independent nearcore witnesses exercising global accounts, wallet hashes and new actions.
   Use a versioned successor harness/fixture generator; immutable old oracle pins do not forbid new
   reference tooling alongside them.

One lane-log boundary claim needs review before integration: its UQ-006 conclusion says distribution
receipts cannot appear in source receipt proofs because they are not instant. At the pin,
`Receipt::is_instant_receipt` defines instant as execution immediately in the same chunk;
`validate_source_receipt_proofs` collects proved receipts and does not impose that instant-receipt
restriction. Non-instant status alone therefore does not establish the claimed impossibility.
Keep this boundary question open until the complete generation/routing path is justified; do not
remove distribution processing from the workplan on the strength of that argument.

## W01 progress and precise remaining work

The [new L7 log](lean-chunk-L7-2026-10-24.md) records the actual comparison repair:

```text
112,036 verdict comparisons in the declared domain
  2,548 asserted domain exclusions
    700 verdict agreements outside the declared domain
115,284 total inputs, partition checked
```

The former 1,259 unasserted exclusions now have licensed classifications. This full accounting was
run against saved verdict outputs, not a new full Lean replay. CLI negative controls cover wrong
verdicts/reasons, missing output, an always-accept checker, wrong successor expectations and timeout.

CI now distinguishes an always-running corpus-free schema check from a conditional real-content job.
`make d3-drivers` and `make d3-smoke` build/run baseline, float, genesis and protocol-gas drivers.
The old claim that CI simply requires an absent `/data/...` directory is superseded. Whether the
conditional content job actually ran remotely was not verified in this audit.

W01 is still partial against its full criteria: drivers do not emit all required observables, so
wrong-gas/refund/log/return/root comparisons are not yet complete; reports lack binding package/binary
identities; full combined-successor expectations/replay remain open. W00's default-target addition
also supersedes parts of the old module-reachability list, which should be recalculated rather than
reusing its historic 50-unreachable-files count.

## Status against every work package

“Integrated” below means the named increment is on main. It does not mean the entire package passed
its frozen-package acceptance criteria.

| Package | Evidence-backed maturity | What prevents completion |
|---|---|---|
| W00 API/boundaries | Interface/owner-map deliverable integrated; default build repaired | Reconcile boundary decisions, stale declarations and unresolved UQs; contracts do not prove runtime semantics |
| W01 harness/CI | Major repair integrated; comparison denominator accounted | Full observables, package identity, exercised corpus-content CI and combined successor expectations |
| W02 capacity | Protocol bound and band demonstration integrated | Fuel/termination/stack/memory audit, size limits, overlap/tier proofs and protocol-boundary stress tests |
| W03 runtime errors | Reproducer/evidence only | Implement pinned LoadingError layout predicate and zero-gas failure parity; resolve other runtime assumptions |
| W04 floats | Kernel and existing evidence integrated | Varied generated whole chunks, overlap proof and cross-feature validation |
| W05 curve hosts | ecrecover/p256/BLS on main; BN128 committed on lane | Branch test repairs, BN128 review/generated validation, runtime host dispatch and valid/invalid chunks per host |
| W06 key families | No new implementation found | secp transaction/delegate verification, ML-DSA arithmetic/codecs/trie representation and end-to-end tests |
| W07 global actions | Additive bodies/tests on main; resolution/checker branch pending | Connect widened actions/receipts/hosts; actual distribution semantics and positive whole chunks |
| W08 resolution/cache | Resolution interfaces on main; L4 wrapper pending | ETH guard integration, pinned cache/deploy semantics and independent resolution fixtures |
| W09 storage | Analysis/proof/interface foundations only | Real recorder and exhaustion/defer/rollback semantics with boundary tests |
| W10 genesis | Corrected checker/replay and configuration adapter integrated | General overlap proof, transaction-flag coverage, validated common successor path |
| W11 resharding | Boundary analysis/interface only | Actual child-state/trie retention, split/congestion/buffers, mixed-epoch decision and validator fixtures |
| W12 combined successor | Config dispatcher and adapters integrated | Crypto/action/recorder/boundary execution integrated together; tier/refinement and cross-family checks |
| W13 authentic replay | No new capture/execution delivery found | Authenticated witnesses and actual execution of 1,000 consecutive blocks across all shards |
| W14 frozen validation | Prior lane/regression evidence only | One frozen combined package, all-family/cross-family/real-window validation, complete proof/runtime audit |
| W15 restricted admission | No new exact-package audit found | Signed live formal-tier report and exact reference build/resource/conformance provenance |
| W16 full release | Blocked | W14 plus successor's own admission, authenticated facts, tier/encoding documentation and authorized release |

The most important remaining chain is now:

```text
W00 interfaces (landed)
  -> runtime host/action/recorder adapters + missing semantic implementations
  -> W12 integrated full successor and tier proofs
  -> W13 representative execution + W14 frozen validation
  -> W16 full successor admission/release
```

W03's known runtime discrepancy, W02 capacity, W06 keys, W09 storage and W11 resharding are substantive
parallel implementation branches, not final polish. W13 witness acquisition and W15 restricted
admission can start without waiting for W12. Do not wait for all arithmetic to be finished before
connecting already implemented hosts through the shared runtime adapter.

## Fresh checks in this audit

- `python3 -m unittest discover -s oracle/tools -p 'test_*.py'`: **50 discovered, 49 passed,
  1 skipped**, exit 0. The skipped test needs `NEAR_CORPORA_DIR` and saved-output configuration;
  this is not “50 executed passes”.
- Coverage generation `--check`: matches pinned source; 222 rows and the status counts above.
- `corpus_manifest.py --verify-schema`: passes for 18 families/6 corpora. Schema validation is not
  a fresh byte-content walk or replay.
- L3 source-interpreted BLS host test: 147 cases, 1 failure, exit 1 (described above).
- L3 missing-fixture BN128 control: `0/0`, exit 0 (described above).
- All nine lane ancestries and working changes inspected. No full clean Lean build, pairing corpus,
  real-window replay or live admission was run for this documentation audit.

## Next actions in dependency order

1. **L0/integration:** consume the landed W00 contracts in real successor host/action dispatch.
   Coordinate the shared `Exec`, `FunctionCall`, D2 successor codec and logged-proof edits.
2. **L3:** reconcile main, fix the two demonstrated runner/test issues, include pending oracle and
   handoff provenance, finish generated BN128/host tests; then submit the incremental integration.
3. **L4:** reconcile W00 interfaces, replace the wrapper-only ETH approach with correct successor
   handling, review UQ-006 and generate positive global-contract fixtures.
4. **L2/Wasm owner:** implement W03 LoadingError parity while expanding W04 chunk fixtures.
5. **L1/L3-key/L5/L6:** run W02, W06, W09 and W11 in parallel under the published interfaces; finish
   W10's narrow proof/test obligations without conflating them with resharding implementation.
6. **L7:** add emitted observables and package identity, provision/verify corpus-content CI, start
   W13 acquisition now and continuously validate integrated paths.
7. **L8:** perform W15's exact-reference admission audit now; W16 waits for the full frozen package.

No new owner or agent was assigned by this audit. Keep each lane's acceptance state and residual
premises in its log; checkpoint merges must not silently change a partial row to validated.
