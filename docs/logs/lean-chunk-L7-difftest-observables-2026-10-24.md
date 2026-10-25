# L7 — difftest observables wired in as a hard failure (P4)

Date: 2026-10-24. Workplan item **P4** in `var/OUTPUTS-PLAN.md` ("Teach
`oracle/v3-d3/tools/difftest_d3.py` to read the `-out` driver's observables, move fields out of
`OBSERVABLES_UNAVAILABLE`, and make observable disagreement a hard failure. Keep the old driver as the
default so nothing existing breaks."). Lane **L7** (differential validation and integration).
Evidence: [docs/evidence/lean-chunk-final-outputs/difftest-observables.md](../evidence/lean-chunk-final-outputs/difftest-observables.md).

## Execution and handoff checklist

| field | value |
|---|---|
| owner | L7 (differential validation and integration) |
| worktree | `/data/illia/nearproof-wt/lean-difftest-obs` |
| branch | `work/difftest-observables` |
| base commit | `5491f7f03` (`main` HEAD at dispatch; "docs: record the output-agreement evidence (result, method, limits)") |
| committed tip | recorded in the reply to the dispatching session; **not merged, not pushed** |
| target | nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86 |
| packages touched | P4 only (`oracle/v3-d3/tools/difftest_d3.py`, plus one stale assertion in `oracle/tools/test_difftest_d3.py` and this lane's docs). **No Lean source, no signed relation, no other lane's file.** |
| language | Python only |
| changed file sha256 | `oracle/v3-d3/tools/difftest_d3.py` `e66a68d4b2e692ec1b8109dde67e271eb5cedecea42a885076dbb9d314e2dacf` (pre-commit working tree; the committed blob's hash is whatever `git log -1 --stat` records) |
| report hashes | d3c9 plain `007987b750186b49ab8f117f4e3c7429db74534f9115cde9a0febed3fed27233`; d3c9 `--lean-out` `066ac8c5be1ba5e7f2eb2b1e1ee447b923424f6d9038a5be4c4fb796dba623a8`; d2corpus.v2 plain `12ad73a1b4c96fe5fd44c0f9e91ff991aa96aee009c22bec97fd2e56eb01a1b8`; d2corpus.v2 `--lean-out` `983ab37d0a2e176bf26cd3d12100be1af481869bd778c6350d3d718df3c386c3` |

Nothing here closes Gate A, B or C. P4 is harness integration, not a semantic package.

## Inventory IDs owned

None. This work changes no coverage-inventory row: P4 wires an existing driver's existing output into an
existing harness. `docs/research/lean-chunk-coverage.json` (schema `near-lean-chunk-coverage-v2`, 222
rows) has no row whose subject is the difftest's observable comparison — the nearest rows are
`L0-EVID-001` … `L0-EVID-004`, which record verdict-level evidence and are owned by L0. This lane claims
no row and edits no row. Row `L0-EVID-001`'s "0 disagreements" remains a *verdict-level* statement; after
this change the same report can additionally carry a field-level statement when `--lean-out` is used,
but the row's own text is unchanged.

## Changed declarations

**No Lean declarations changed.** Python only. The edited Python surface:

| file | change |
|---|---|
| `oracle/v3-d3/tools/difftest_d3.py` | added `--lean-out` and `--d2` flag parsing; added `LEAN_OUT`, `D2_CHECK`, `CLAIM_OUTPUTS` paths; added `D2_EXCLUSION_LICENSES`; added `OBSERVABLES_COMPARED_VS_CLAIM`, `OBSERVABLES_EMITTED_BUT_NOT_COMPARED`; added `claim_module()`, `independent_outputs()`, `compare_observables()`; threaded `exe`/`prefix` through `run_checker()`; threaded `licenses` through `exclusion_asserted()`/`compare()`; added the observable block and `observable_comparison` key to the report; added a silent-downgrade invariant |
| `oracle/tools/test_difftest_d3.py` | replaced one stale assertion. It asserted `"gas_burnt" in doc["observables"]["unavailable"]`, which no version of the script ever satisfied — the test was red at the base commit. It now asserts the actual contract: unavailable names `refunds`/`tx_results`, the default `checked` list excludes the claim-comparable fields, `gasBurnt` is not in `unavailable`, and `observable_comparison` is absent without `--lean-out` |

No signature or meaning change to any pre-existing public key of `near-d3-difftest-report-v1`.

## Build and test commands run

```sh
cd /data/illia/nearproof-wt/lean-difftest-obs

# syntax
python3 -c "import ast;ast.parse(open('oracle/v3-d3/tools/difftest_d3.py').read())"

# harness self-tests (22 tests, 1 skipped: needs NEAR_CORPORA_DIR)
python3 -m unittest oracle.tools.test_difftest_d3

# default path byte-identical to base, full corpus
git show 5491f7f03:oracle/v3-d3/tools/difftest_d3.py > /tmp/obsverify-difftest-obs/base.py
python3 /tmp/obsverify-difftest-obs/base.py /data/illia/nearproof-deps/corpora/d3c9 --shards 12 --report /tmp/obsverify-difftest-obs/d3c9-base.json
python3 oracle/v3-d3/tools/difftest_d3.py        /data/illia/nearproof-deps/corpora/d3c9 --shards 12 --report /tmp/obsverify-difftest-obs/d3c9-plain.json
cmp /tmp/obsverify-difftest-obs/d3c9-base.json /tmp/obsverify-difftest-obs/d3c9-plain.json

# D3 observables
python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d3c9 --shards 12 --lean-out --report /tmp/obsverify-difftest-obs/d3c9-out.json

# D2 observables
python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d2corpus.v2 --shards 12 --d2 --lean-out --report /tmp/obsverify-difftest-obs/d2-out.json
```

No Lean build was needed: the drivers `nearspec-v3-check-d3`, `nearspec-v3-check-d3-out` and
`nearspec-v3-check-d2` already exist as compiled artifacts. They were **copied** (not hard-linked) into
this worktree's ignored `.lake/build/bin/` so the default path resolves here:

| binary | sha256 |
|---|---|
| `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3` | `58c10b50849ce9f13321c5b11fa536b7ec7a276c120bb7dd6be352905e247cda` |
| `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out` | `6ec0e691af1c9c4038ee62e1c20cf32f41c82bc91f585a9aee84af5580daa64a` |
| `spec/lean/v3/.lake/build/bin/nearspec-v3-check-d2` | `47bdd50c84a02cd9ea12efbdde499889a653576f979617b6b4f00fe196c322c9` |

`.lake/` is git-ignored, so these copies are not committed and do not appear in the diff. They exist only
so the runs below execute in this worktree.

## Results

### Default path unchanged (byte-identical)

| run | exit | report sha256 |
|---|---|---|
| base script, d3c9 | 0 | `007987b750186b49ab8f117f4e3c7429db74534f9115cde9a0febed3fed27233` |
| new script, d3c9 | 0 | `007987b750186b49ab8f117f4e3c7429db74534f9115cde9a0febed3fed27233` |

`cmp` reports no difference; stdout differs only in the report path. The default run also produces no
`observable_comparison` key and leaves `observables.checked` at `["verdict", "domain_exclusion_reason"]`.

### d3c9 — plain vs `--lean-out`

| quantity | plain | `--lean-out` |
|---|---|---|
| cases | 15,995 | 15,995 |
| exit | 0 | 0 |
| `total_disagreements` | 0 | 0 |
| verdict partition | 342 / 100 / 15,553 | identical |
| accepted cases with observables compared | — | 5,715 |
| non-accepted cases with null outputs | — | 10,280 |
| field mismatches | — | 0 |
| observable failures | — | 0 |

Per family: `d3` 2,656; `mutants` 2,959; `ood` 100. Case-by-case verdict/reason/classification
regressions against the plain run: **0**.

### d2corpus.v2 — `--d2` plain vs `--d2 --lean-out`

| quantity | plain | `--d2 --lean-out` |
|---|---|---|
| cases | 67,384 | 67,384 |
| exit | 0 | 0 |
| `total_disagreements` | 0 | 0 |
| verdict partition | 390 / 66,994 | identical |
| accepted cases with observables compared | — | 17,738 |
| non-accepted cases with null outputs | — | 49,646 |
| field mismatches | — | 0 |
| observable failures | — | 0 |

Per family: `d2` 10,537; `mutants` 7,201; `ood` 0. Regressions against the plain run: **0**.

### Totals

83,379 cases; 23,453 accepted cases' observables compared; 211,077 individual field comparisons; 0
mismatches; 0 observable failures; both runs exit 0. The comparison is field-by-field against an
independent Python decode of each case's `claim.bin`, not verdict agreement.

## Failing cases

**None in the honest runs.** Every failure in this session is a deliberate perturbation:

| perturbation | scope | observable failures | exit |
|---|---|---|---|
| honest driver | d3c9 `d3`, 200 cases | 0 | 0 |
| `gasBurnt += 1` on the first accepted line | same 200 | 4 | **1** |
| `stateRoot` last hex digit flipped | same 200 | 4 | **1** |
| `proposals` replaced | same 200 | 4 | **1** |
| `outputs := null` on the first accepted line | same 200 | 4 | **1** |
| outputs attached to the first rejected line | d3c9 `mutants`, 200 | 4 | **1** |

In every perturbed run the verdict partition stays identical to the honest run
(`verdict_compared_agree` 200, 0 verdict disagreements) and the run still exits 1: the failure is the
observable comparison. One further negative control: `--lean-out --lean-from <plain-driver save>` prints
`FAIL:` and exits 1 rather than writing a verdict-only report.

## What this does not establish

* The five fields still in `OBSERVABLES_UNAVAILABLE` (`refunds`, `return_data`, `validator_rewards`,
  `tx_results`, `action_results`) are neither emitted nor compared. **No field moved out of that list**,
  because none of them was ever emitted. The task brief's "move fields out" anticipated a list that
  contained emitted fields; it does not. What moved is the report's other observable keys: `checked` gains
  the nine compared field names only under `--lean-out`, and two new keys separate *compared*
  (`compared_vs_claim`) from *emitted but not compared* (`emitted_but_not_compared`:
  `congestion`, `bwRequests`, `logs`, `receiptCount`, `wasmGas`).
* The five emitted-but-uncompared fields have no independent value in `claim.bin`, so this harness cannot
  check them. `wasmGas` and log count are cross-checked against nearcore's feature record by a different
  script (`tools/d3/check_nearcore_features.py`).
* Rejected and out-of-domain cases emit no outputs by design; their computed values are not compared.
* No nearcore equivalence theorem. The comparison is against the claim header's endorsed fields; the
  signed checker's `accepted_observable_agrees` is what licenses reading an accepted case's printed
  outputs as its computed outputs.

## Open items with concrete next steps

1. **The five unavailable fields are still unavailable.** Closing them needs the signed checker to emit
   refunds, return data, validator rewards, tx results and action results — a Lean change this lane must
   not make. Next step: hand the field list to the lane that owns the observable record and ask for an
   additive emission.
2. **The five emitted-but-uncompared fields need an independent source.** `congestion`, `bwRequests`,
   `logs`, `receiptCount` and `wasmGas` are computed values the claim does not carry. `wasmGas` and log
   count already have one (`meta.json`'s feature record); the other three would need nearcore to record
   them per case. Next step: extend `tools/d3/check_nearcore_features.py` to the remaining fields rather
   than claiming them in the difftest.
3. **The default path cannot run in a fresh worktree without copied binaries.** This lane copied three
   compiled drivers into its ignored `.lake/build/bin/`. A CI job that wants the default path needs a Lean
   build first. Next step: add a build step to the difftest CI job (or accept `D3_CHECK` as a required
   environment variable).
4. **A pre-existing red test is now green, but the rest of the suite's corpora-gated test remains
   skipped.** `RealCorpora.test_real_population_partition` skips without `NEAR_CORPORA_DIR`. Next step:
   set it in the corpora-enabled CI job so the population accounting is measured, not skipped.
5. **`--d2 --python` is refused, not implemented.** The D2 Python difftest lives in
   `oracle/tools/difftest_v3_d2.py` and was not run here. Next step: if a three-way D2 comparison is
   wanted in this script, port that leg rather than pointing at another script.

## Safe-to-edit files

Other lanes may edit these without colliding with this change:

* Any Lean source. This change touches none.
* `tools/d3/check_outputs.py`, `tools/d3/check_output_mutants.py`,
  `tools/d3/check_nearcore_features.py`. This change imports `tools/d3/claim_outputs.py` but edits no file
  under `tools/d3/`.
* `oracle/tools/difftest_v3_d2.py` and the `spec_check_v3_*` Python checkers.
* Every coverage-inventory JSON and generator.
* `var/OUTPUTS-PLAN.md` (read for P4, not edited).

Files this change owns — expect a conflict if another lane edits them:

* `oracle/v3-d3/tools/difftest_d3.py` (the only functional change)
* `oracle/tools/test_difftest_d3.py` (one assertion replaced)
* `docs/evidence/lean-chunk-final-outputs/difftest-observables.md` (new)
* this log

## Next executable step

Hand P4's result to the integration owner: the difftest now compares nine consensus fields per accepted
case against an independent claim decode and treats any disagreement as a hard failure, verified on
83,379 cases across d3c9 and d2corpus.v2 with zero mismatches and zero verdict regressions. The open
items above are the remaining honest gaps; item 1 is the only one that needs a Lean change.
