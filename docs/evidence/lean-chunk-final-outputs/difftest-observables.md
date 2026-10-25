# The difftest now compares emitted observables, and a disagreement is a hard failure

Worktree `/data/illia/nearproof-wt/lean-difftest-obs`, branch `work/difftest-observables`, base commit
`5491f7f03`. Workplan item **P4** (`var/OUTPUTS-PLAN.md`, "difftest integration"). Python only: no Lean
source and no signed relation was touched.

## The gap this closes

`oracle/v3-d3/tools/difftest_d3.py` compared **verdicts and reasons only**. Its module docstring
documented an observable driver `nearspec-v3-check-d3-out` and a `--lean-out` option, but `--lean-out`
was never parsed — the string appeared only in comments. So the report declared
`OBSERVABLES_UNAVAILABLE = ["refunds","return_data","validator_rewards","tx_results","action_results"]`
and listed `OBSERVABLES_EMITTED_BY_OUT_DRIVER`, while the harness never read or compared a single emitted
observable. A reader could see "0 disagreements" and reasonably, but wrongly, believe the outputs had
been checked.

## What changed

`oracle/v3-d3/tools/difftest_d3.py` only. No Lean file, no signed relation, no other lane's file.

1. **`--lean-out` is parsed** and runs `nearspec-v3-check-d3-out` as the Lean leg instead of the plain
   checker. With `--d2` it runs the same driver with `--d2` (the D2 pipeline), and the plain D2 driver
   `nearspec-v3-check-d2` is the default Lean leg when `--d2` is given without `--lean-out`.
2. **Observables are compared per accepted case against an independent decode of `claim.bin`.** The
   decoder is `tools/d3/claim_outputs.py` (`decode_claim`, `decode_chunk_inner`), imported — not
   re-implemented — and the field mapping mirrors `tools/d3/check_outputs.py` (`SCALAR_FIELDS` +
   `proposals`). Nine fields are compared:
   `stateRoot`, `outcomeRoot`, `gasBurnt`, `balanceBurnt`, `outgoingReceiptsRoot`, `proposals`,
   `txRoot`, `encodedMerkleRoot`, `encodedLength`.
3. **A disagreement is a hard failure.** Six buckets are failures and each is added to
   `total_disagreements`, so the process exits 1:

   | bucket | meaning |
   |---|---|
   | `accepted_observables_disagree` | an accepted case whose emitted field differs from the claim decode |
   | `accepted_null_outputs` | an accepted case whose `outputs` is null |
   | `accepted_missing_outputs` | an accepted case whose line has no `outputs` key |
   | `nonaccepted_with_outputs` | a reject/out-of-domain case that wrongly emitted outputs |
   | `claim_decode_error` | `claim.bin` failed to decode |
   | `observable_missing_line` | counted in the partition for completeness; the verdict comparison already owns it as `missing_output`, so it is **not** added again to `total_disagreements` |

4. **The unavailable list is now honest.** No field moved out of `OBSERVABLES_UNAVAILABLE`, because none
   of the five was ever emitted or compared: `refunds`, `return_data`, `validator_rewards`, `tx_results`
   and `action_results` are still unavailable. What changed is the report's other observable keys: with
   `--lean-out`, `observables.checked` gains the nine compared field names and two new keys appear,
   `compared_vs_claim` and `emitted_but_not_compared` (`congestion`, `bwRequests`, `logs`, `receiptCount`,
   `wasmGas` — computed values the claim does not carry, so they are explicitly *not* claimed as
   compared). The top-level key `observable_comparison` carries the partition, per-field mismatch counts,
   and up to 200 failures.
5. **Report schema is additive.** `near-d3-difftest-report-v1` is unchanged for a default run; the new
   keys appear only when `--lean-out` produced the lines. Per-case rows gain `observable_compared`,
   `observable_agrees`, `observable_fields_compared` and `observable_classification`; no existing key
   changes meaning or type.
6. **A silent downgrade is refused.** If `--lean-out` is requested but the Lean lines carry no `outputs`
   key (e.g. a `--lean-from` file saved from the plain driver), the run prints `FAIL:` and exits 1 rather
   than writing a verdict-only report. A post-loop invariant enforces the same thing: `--lean-out` with
   no observable comparison is a failure.
7. **`--d2 --python` is refused** with a message pointing at `oracle/tools/difftest_v3_d2.py`. This
   script's Python leg is the D3 checker; running it over D2 metadata would report a relation mismatch as
   a disagreement.

## Commands, corpora, counts, exit codes

All commands run from `/data/illia/nearproof-wt/lean-difftest-obs`. Reports and logs are kept under
`/tmp/obsverify-difftest-obs/` (a run-unique directory; an earlier attempt reused `/tmp/obsrun` and a
concurrent process overwrote one report, so every number below was re-generated cleanly here).

### Default path is byte-identical to the base commit

The base script (`git show 5491f7f03:…`) and the new script were run on the full d3c9 corpus with the
same arguments and no `--lean-out`:

```sh
git show 5491f7f03:oracle/v3-d3/tools/difftest_d3.py > oracle/v3-d3/tools/_base_difftest_d3.py
python3 oracle/v3-d3/tools/_base_difftest_d3.py /data/illia/nearproof-deps/corpora/d3c9 \
  --shards 12 --report /tmp/obsverify-difftest-obs/d3c9-base.json > /tmp/obsverify-difftest-obs/d3c9-base.log 2>&1
python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d3c9 \
  --shards 12 --report /tmp/obsverify-difftest-obs/d3c9-plain.json > /tmp/obsverify-difftest-obs/d3c9-plain.log 2>&1
cmp /tmp/obsverify-difftest-obs/d3c9-base.json /tmp/obsverify-difftest-obs/d3c9-plain.json   # byte-identical
diff <(grep -v 'wrote report' d3c9-base.log) <(grep -v 'wrote report' d3c9-plain.log)  # empty
```

| run | exit | report sha256 |
|---|---|---|
| base script, d3c9 plain | 0 | `007987b750186b49ab8f117f4e3c7429db74534f9115cde9a0febed3fed27233` |
| new script, d3c9 plain | 0 | `007987b750186b49ab8f117f4e3c7429db74534f9115cde9a0febed3fed27233` |

The default run's stdout and report are byte-identical: same partition, same 15,995 per-case records, same
exit code. The default path pays nothing for the new code — the claim decoder is imported lazily and only
under `--lean-out`.

### D3: d3c9, plain vs `--lean-out`

```sh
python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d3c9 \
  --shards 12 --report /tmp/obsverify-difftest-obs/d3c9-plain.json --save /tmp/obsverify-difftest-obs/d3c9-plain
python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d3c9 \
  --shards 12 --lean-out --report /tmp/obsverify-difftest-obs/d3c9-out.json --save /tmp/obsverify-difftest-obs/d3c9-out
```

| quantity | plain | `--lean-out` |
|---|---|---|
| inputs | 15,995 | 15,995 |
| exit | 0 | 0 |
| `total_disagreements` | 0 | 0 |
| verdict partition | `domain_exclusion_asserted` 342, `verdict_agree_outside_domain` 100, `verdict_compared_agree` 15,553 | identical |
| observable partition | — | `accepted_observables_agree` 5,715, `nonaccepted_no_outputs` 10,280 |
| field mismatches | — | 0 |
| observable failures | — | 0 |

Per-family accepted cases whose observables were compared: `d3` 2,656; `mutants` 2,959; `ood` 100
(total 5,715). The remaining 10,280 cases are reject/out-of-domain and correctly emit `outputs: null`.

Verdict regression check against the plain run, case by case: **0** differences in
`(verdict, reason, classification)` across all 15,995 cases; the case sets are identical.

### D2: d2corpus.v2, plain vs `--d2 --lean-out`

```sh
python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d2corpus.v2 \
  --shards 12 --d2 --report /tmp/obsverify-difftest-obs/d2-plain.json
python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d2corpus.v2 \
  --shards 12 --d2 --lean-out --report /tmp/obsverify-difftest-obs/d2-out.json
```

| quantity | plain | `--d2 --lean-out` |
|---|---|---|
| inputs | 67,384 | 67,384 |
| exit | 0 | 0 |
| `total_disagreements` | 0 | 0 |
| verdict partition | `domain_exclusion_asserted` 390, `verdict_compared_agree` 66,994 | identical |
| observable partition | — | `accepted_observables_agree` 17,738, `nonaccepted_no_outputs` 49,646 |
| field mismatches | — | 0 |
| observable failures | — | 0 |

Per-family accepted cases whose observables were compared: `d2` 10,537; `mutants` 7,201; `ood` 0 (total
17,738). Verdict regression check against the plain run, case by case: **0** differences in
`(verdict, reason, classification)` across all 67,384 cases.

### Totals across both corpora

| corpus | cases | accepted, observables compared | field comparisons | mismatches | failures | exit |
|---|---|---|---|---|---|---|
| d3c9 | 15,995 | 5,715 | 51,435 | 0 | 0 | 0 |
| d2corpus.v2 | 67,384 | 17,738 | 159,642 | 0 | 0 | 0 |
| **sum** | **83,379** | **23,453** | **211,077** | **0** | **0** | **0** |

`field comparisons` = accepted cases × 9 compared fields. These are field-level comparisons against an
independent Python decode of each case's `claim.bin`, not verdict agreement.

## The flag changes behaviour: a perturbed observable is caught

Five perturbation wrappers were generated under `/tmp/obsverify-difftest-obs/perturb/`. Each one shells
out to the real driver, parses its JSON lines, mutates exactly one aspect on the first matching line of
each shard process, and re-prints the rest untouched. Verdicts and reasons pass through unchanged, so the
only difference from an honest run is the observable.

```sh
D3_CHECK_OUT=/tmp/obsverify-difftest-obs/perturb/w_gas.py \
  python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d3c9 \
  --only d3 --sample 200 --shards 4 --lean-out \
  --report /tmp/obsverify-difftest-obs/perturb/p_gas.json
```

| wrapper | perturbation | verdicts | observable failures | `total_disagreements` | exit |
|---|---|---|---|---|---|
| — (honest) | none | 0 | 0 | 0 | 0 |
| `w_gas` | `outputs.gasBurnt += 1` on the first accepted line | 0 | 4 | 4 | **1** |
| `w_stateroot` | last hex digit of `outputs.stateRoot` flipped | 0 | 4 | 4 | **1** |
| `w_proposals` | `outputs.proposals` replaced | 0 | 4 | 4 | **1** |
| `w_nullouts` | `outputs` set to `null` on the first accepted line | 0 | 4 | 4 | **1** |
| `w_outs_on_reject` | outputs attached to the first rejected line (run on `mutants`) | 0 | 4 | 4 | **1** |

The honest baseline for the same 200-case `d3` sample: `accepted_observables_agree` 200, failures 0,
exit 0. For `w_outs_on_reject` the honest baseline is the 200-case `mutants` sample
(`accepted_observables_agree` 36, `nonaccepted_no_outputs` 164, failures 0, exit 0); the wrapper turns
four of those 164 into `nonaccepted_with_outputs` and the run exits 1. Each wrapper leaves the verdict partition **identical** (`verdict_compared_agree` 200) and still
fails the run — the failure comes from the observable comparison, not from a verdict change. That is the
property the flag exists to provide.

Example emitted line from the `w_gas` run (report `observable_comparison.failures[0]`):

```json
{"case": ".../d3c9/d3/00-h10005-s1", "problem": "observables disagree on 1 field(s) ['gasBurnt']",
 "mismatches": [{"field": "gasBurnt", "emitted": 2506937184306, "claim": 2506937184305}]}
```

### The failure paths that are not field mismatches also fail

| path | how exercised | result |
|---|---|---|
| `accepted_null_outputs` | `w_nullouts` | 4 failures, exit 1 |
| `nonaccepted_with_outputs` | `w_outs_on_reject` on `mutants` | 4 failures, exit 1 |
| `missing_observables` | `--lean-out --lean-from <plain-driver save>` | `FAIL:` on stderr, exit 1, no verdict-only report |
| `--d2 --python` | flag combination | refused with a pointer to `oracle/tools/difftest_v3_d2.py`, exit 1 |

## What this does and does not establish

**Establishes.** For every accepted case in d3c9 and d2corpus.v2 — 23,453 cases — the nine consensus
fields Lean's output driver printed are byte-equal to an independent Python decode of that case's
`claim.bin`. A disagreement in any of those fields, a missing or null output on an accepted case, outputs
on a non-accepted case, or an undecodable claim makes the run exit 1. The comparison runs in the same
process and report as the verdict comparison, so "0 disagreements" in this report now covers both.

**Does not establish.**

* **Nothing about the five unavailable fields.** `refunds`, `return_data`, `validator_rewards`,
  `tx_results` and `action_results` are not emitted by the driver and are not compared. They remain in
  `OBSERVABLES_UNAVAILABLE`.
* **Nothing about the five emitted-but-uncompared fields.** `congestion`, `bwRequests`, `logs`,
  `receiptCount` and `wasmGas` are computed values the claim does not record, so there is no independent
  value to compare them against in this harness. They are listed as `emitted_but_not_compared`, not as
  checked. (`wasmGas` and log count *are* cross-checked against nearcore's independent feature record by
  `tools/d3/check_nearcore_features.py`; that is a different script and a different comparison.)
* **Nothing about rejected cases' computed values.** The signed checker does not expose partial state on
  a failing path, so a rejected case's outputs are null by design. Rejected cases are checked by verdict
  and reason only.
* **Nothing about cases outside these two corpora.** These are differential tests over the cases on disk.
* **No nearcore equivalence theorem.** The comparison is against the claim header's endorsed fields. That
  the signed checker proved its computed values equal those fields on acceptance
  (`NearSpecV3.accepted_observable_agrees`) is what makes the comparison meaningful; it is not a proof
  that a nearcore validator would recompute the same values on arbitrary inputs.

## Reproduce

```sh
cd /data/illia/nearproof-wt/lean-difftest-obs
D=/tmp/obsverify-difftest-obs; mkdir -p $D

# 1. default path byte-identical to base
git show 5491f7f03:oracle/v3-d3/tools/difftest_d3.py > $D/base.py
python3 $D/base.py /data/illia/nearproof-deps/corpora/d3c9 --shards 12 --report $D/base.json 2>&1 | tail -2
python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d3c9 --shards 12 --report $D/new-plain.json 2>&1 | tail -2
cmp $D/base.json $D/new-plain.json && echo BYTE-IDENTICAL

# 2. D3 observables
python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d3c9 --shards 12 --lean-out --report $D/d3c9-out.json

# 3. D2 observables
python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d2corpus.v2 --shards 12 --d2 --lean-out --report $D/d2-out.json

# 4. perturbation control (must exit 1)
D3_CHECK_OUT=/tmp/obsverify-difftest-obs/perturb/w_gas.py \
  python3 oracle/v3-d3/tools/difftest_d3.py /data/illia/nearproof-deps/corpora/d3c9 \
  --only d3 --sample 200 --shards 4 --lean-out --report $D/perturb.json

# 5. harness self-tests
python3 -m unittest oracle.tools.test_difftest_d3
```

Exit 0 only when the failure count is zero. The perturbation control in step 4 must exit 1.
