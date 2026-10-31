# Gate-B freeze: harness reconciled, stored verdicts rescored (2026-10-31)

Freeze replay at main `2368b8713`, checker `nearspec-v3-check-successor` sha256 `9b583e3a…`.
Inputs, verdicts and the original reports are in `/data/illia/nearproof-deps/gateb-freeze-2368b8713/`;
the rescored reports are in its `rescore-2026-10-31/<run>/report.json`, and `summary.json` here
holds their partitions, reclassification and sha256. **The checker was not re-executed and nothing
in its semantics changed.** Only the comparison (`tools/d3/replay_successor.py` →
`oracle/v3-d3/tools/difftest_d3.py compare`, plus the new `oracle/tools/independent_domain.py`) moved.

```
python3 tools/d3/replay_successor.py --rescore $G/<run> --out $G/rescore-2026-10-31/<run>
```

`--rescore` refuses unless `results.jsonl` is the file the run's report hashed and every input
(`claim.bin`, `witness.bin`, `meta.json`) still has the sha256 recorded before the original run.
All six runs with stored verdicts passed that check.

## Result

| run | cases | before | after | disagreements after |
|---|---|---|---|---|
| census-allFeatures | 3,138 | pass | pass | 0 |
| census-signed | 3,138 | pass | pass | 0 |
| corpus-cases-allFeatures | 235,716 | fail (95) | **pass** | 0 |
| corpus-cases-signed | 235,716 | fail (245) | **pass** | 0 |
| fixtures-final-allFeatures | 1,364 | fail (14) | **pass** | 0 |
| fixtures-final-signed | 1,364 | fail (204) | **pass** | 0 |

The four other run directories (`fixtures-{allFeatures,signed}`, `fixtures-meta-{allFeatures,signed}`)
hold no verdicts: they aborted before running the checker on a missing input (`d1-genesis-flag`
cases without `meta.json`; an unpacked `seed61-00-h10061-s5` witness). `fixtures-final` is the
corrected 1,364-case list; `--rescore` refuses the aborted ones. `shard13-*.jsonl` is raw checker
output, not a replay.

## Old → new classification (only the rows that moved; every other row has the same bucket)

| run | rows | before | after | why |
|---|---|---|---|---|
| corpus-cases-allFeatures | 95 | `domain_exclusion_where_in_domain` | `domain_exclusion_asserted` | rule 1: race reason, oracle label `e.code_cache` (pre-W08 corpora) |
| corpus-cases-signed | 128 | `domain_exclusion_unasserted` | `domain_exclusion_independently_asserted` | `c.not_genesis`: B2's `prev_hash` is zero |
| | 62 | 〃 | 〃 | `w.shape` non-ED25519 tx key: a tx signer key tag ≠ 0 |
| | 48 | 〃 | 〃 | `w.shape` ML-DSA-65 key: a key with tag 2 in a tx or receipt |
| | 4 | 〃 | 〃 | `c.segment`: more than 32 blocks |
| | 3 | 〃 | 〃 | `e.wasm-α` cache-served: pre-state code absent from the witness, deployed earlier in the chunk |
| fixtures-final-allFeatures | 12 | `domain_exclusion_unasserted` | `domain_exclusion_independently_asserted` | race reason on pipeline-race fixtures (oracle: `w.shape` only): a call served only by an earlier in-chunk deploy |
| | 2 | `domain_exclusion_where_in_domain` | `race_exclusion_conservative` | see "real disagreement" below |
| fixtures-final-signed | 200 | `accept_above_g_alpha` | `accept_above_g_alpha_agree` | rule 3: all 200 nearcore-valid (96 `e.g_alpha`, 104 `w.size`+`e.g_alpha`) |
| | 2 | `domain_exclusion_unasserted` | `domain_exclusion_independently_asserted` | `w.size` 8 MiB: state witness > 8,388,608 B |
| | 2 | 〃 | 〃 | `w.shape` GlobalContractDistribution receipt (resharding-fixtures-2, seed67) |

Total moved: 95 + 245 + 14 + 204 = 558 rows, i.e. the 558 failures before. 0 rows moved into a
failing bucket.

## Rules

1. **Race exclusion.** `out of domain (e.code_prep_race)` counts as the compiled-contract-cache
   exclusion. Only a race label licenses it: `e.code_cache` on the pre-W08 corpora and
   `e.code_prep_race` on the successor corpora. `e.code_deploy_served` never licenses it. The
   pre-W08 `e.code_cache` label also covered deploy-served cases. On the 95 corpus rows it covers,
   nearcore rejects all 95 (W08 §6).
2. **Independent licence** (`independent_domain.py`). Some exclusions have no matching label in the
   oracle's `d3_violations`. Most of these rows come from the D1/D2 `ood` families: their
   `d3_violations` is empty and their labels sit in `d1_/d2_violations`. Such an exclusion passes
   only when all three conditions hold:
   - the reason text is exactly one the module knows;
   - the tier still excludes that shape;
   - the predicate, computed in Python from the decoded `claim.bin`/`witness.bin`, holds.

   The decoders are the independent reference's (`spec_check_v3.py`, `v3lib/near2.py` in lenient
   walk mode). Nothing reads Lean output.
3. **Signed G_α.** `D3.checkD3_cases` (`D3/Signed.lean`): off the legacy core, `checkD3` is
   `signedRecorderCheck Wasm.pv86 none`, so it has no gas cap. On the signed tier, an accept above
   G_α is compared with nearcore. Agreement passes and disagreement fails.

## Validation of the predicates

- **Cross-tabulation against the checker's own verdicts.**
  - Populations: all 1,364 signed fixtures, plus 37,283 signed corpus rows (every `ood` and
    out-of-domain row, plus 30,000 sampled others).
  - Every one of the 245 + 4 newly licensed rows has its predicate true.
  - On rows the checker accepts, these predicates are never true: `b2_is_genesis`, `segment`,
    `8 MiB`, non-ED25519, ML-DSA and GCD.
- **Weaker predicates.** Two predicates are necessary conditions, not exact ones:
  - `prestate_code_absent_but_deployed_in_chunk` is true on 2 of 13,625 sampled accepts. In
    each, the call's receipt is not executed in this chunk (delayed).
  - `call_served_by_earlier_in_chunk_deploy` names the structural precondition of the race, not
    the race itself. It is true on 12 of the 13,625 sampled corpus accepts.

  A static decode cannot see receipt delays or scheduling. Both predicates are used only to
  license an exclusion the checker already made.
- **Breakage control on the real rows.**
  - Rotating the reason of every newly licensed row to another known reason fails 244 of 245
    signed corpus rows. The 245th, `d2corpus.v2/ood/12-h10003-s0`, really has both properties:
    its B2 is genesis and it has a non-ED25519 tx key.
  - The same rotation fails 4/4 signed fixture rows, 14/14 allFeatures fixture rows and 95/95
    allFeatures corpus rows.
  - Flipping nearcore's verdict on the 200 above-G_α accepts fails all 200.

## Real checker-vs-oracle disagreement: 2 conservative race exclusions

`w08-warm-cache/cases/cc802-00-h10004-s2-code.none` and `cc803-00-h10004-s2-code.none` are
labelled `e.code_deploy_served`, so they are in domain for allFeatures. Nearcore rejects both, with
the same verdict under both forced schedules. Only the failure point moves: eager gives
`MissingTrieValue` on `9hpm…` (TINY), lazy gives it on `4yin…` / `HwjD…` (`d3rich`). The checker
reports `out of domain (e.code_prep_race)`.

These two are a **real domain disagreement**: the checker excludes chunks that nearcore decides
deterministically. They are 2 of W08's 27 conservative `code.none` exclusions (W08 §4, §7). They
are a completeness gap, not a soundness issue: nothing is accepted that nearcore rejects. They pass
only as `race_exclusion_conservative`, which requires both of these:
- nearcore's own schedule probe (`nearcore_schedule`) shows the same verdict at different failure
  points;
- the decode finds a deploy-served call.

They are listed under `known_gaps` in the report. Deciding them would require the checker to
continue past the racing call to the next certain failure. That work is still open (W08 §7).

The 12 pipeline-race fixture rows are similar: Lean's pipeline model marks a chunk with a
global-contract call as `uncertain`. Nearcore's cold run accepted 8 of them and rejected 4. No forced-schedule
probe exists for this family, so whether nearcore can race there is not established. They are
licensed by the structural predicate on cases the oracle already places outside D3α (`w.shape`).
They are also conservative exclusions.
