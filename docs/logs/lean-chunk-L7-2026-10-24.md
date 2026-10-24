# L7 — W01 harness and CI repair (handoff)

Date: 2026-10-24. Plan lane: `docs/requirements/LEAN_CHUNK_COMPLETION_WORKPLAN.md` §"W01 Harness and
CI repair". Predecessor log: [lean-chunk-L7-2026-10-23.md](lean-chunk-L7-2026-10-23.md).
Dispatch note: [lean-chunk-parallel-execution-2026-10-23.md](lean-chunk-parallel-execution-2026-10-23.md) §2.1, §2.2, §4.

## Execution and handoff checklist

| field | value |
|---|---|
| owner | L7 (differential validation and integration) |
| worktree | `/data/illia/nearproof-wt/lean-chunk-L7` |
| branch | `lane/lean-chunk-L7` |
| base commit | `46ddb874692225cbafdd7bc5cac9baa3834ae2b6` (`main` HEAD at dispatch) |
| committed tip | recorded in the reply; **not merged, not pushed** |
| target | nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86 |
| packages touched | W01 only (CI + D3 harness + manifest tool). No Lean source, no signed surface, no other lane's file. |

Nothing here closes Gate A, B or C. W01 is a harness/CI repair, not a semantic package.

---

## 1. What was actually broken, and what changed

### 1.1 The merged CI job failed on every hosted push (reproduced)

The merged `difftest-gates` job ran

```
python3 tools/d3/corpus_manifest.py --verify docs/evidence/lean-chunk-L7/corpus-manifest.json
```

with no `--corpora`. The script defaulted to the developer-local
`/data/illia/nearproof-deps/corpora`, so on a GitHub-hosted runner the directory is absent and the
script exits 1. Reproduced before any change:

```
$ python3 tools/d3/corpus_manifest.py --verify docs/evidence/lean-chunk-L7/corpus-manifest.json --corpora /nonexistent/corpora
corpora directory not found: /nonexistent/corpora
EXIT=1
```

That is a permanently red check, which is worse than no check.

### 1.2 The comparison hole: 1,259 verdicts compared to nothing (reproduced exactly)

`oracle/v3-d3/tools/difftest_d3.py`'s `compare()` short-circuited on the `g_alpha` and `code_cache`
classifier branches before the accept/reject equality test. I re-implemented the control flow and ran
it over the 115,284 saved Lean verdicts plus on-disk `meta.json`. The population arithmetic is exact:

| population | count |
|---|---|
| all cases | 115,284 |
| `out_of_domain` verdicts | 2,548 |
| — of which the `g_alpha` classifier branch applied | 1,010 |
| — of which the `code_cache` classifier branch applied | 279 |
| — **reaching neither classifier branch** | **1,259** |
| accept/reject verdicts actually compared | 112,736 |

1,010 + 279 + 1,259 = 2,548, and 112,736 + 2,548 = 115,284. The 1,259 figure is the `ood` family's
2,269 exclusions minus the 1,010 that carry an `e.g_alpha` mark. A naive count from `meta.json` gives
2,269 and is wrong for exactly that reason.

The 1,259 by reason code (measured from the saved verdicts):

| reason code | count |
|---|---|
| `e.wasm-α` | 710 |
| `w.shape` | 373 |
| `c.not_genesis` | 137 |
| `e.secp` | 36 |
| `c.segment` | 3 |
| **total** | **1,259** |

This matches the brief's breakdown exactly. My trace did not disagree with the stated figure.

### 1.3 Changes

**`tools/d3/corpus_manifest.py`** — removed the hardcoded developer path and split the two checks
that the workplan requires to stay distinct:

* `--verify-schema FILE` — corpus-free shape check. Validates the document's schema string, required
  keys, non-negative integer counts, 64-char lowercase hex digests, and that the counts name the same
  corpora as the families map. Reads no corpus bytes. Always runnable.
* `--verify FILE` — the content drift gate. Re-walks the corpora and compares every family's cases,
  bytes, digest, and `missing_count`, plus the per-corpus totals. Requires `--corpora DIR` or
  `NEAR_CORPORA_DIR`.
* Exit codes are distinct and meaningful: **2** = corpora root not configured (usage), **1** =
  configured-but-absent or genuine drift. The manifest's recorded `corpora_root` is treated as
  provenance and is not compared against the current host path.
* A malformed manifest now fails the content gate too (schema is re-validated before the walk).

**`oracle/v3-d3/tools/difftest_d3.py`** — `compare()` now classifies every input exactly once and
asserts the partition sum equals the input count. New contract:

| bucket | meaning | gate |
|---|---|---|
| `missing_output` | no verdict line for the case | **fail** |
| `malformed_verdict` | verdict outside accept/reject/out_of_domain | **fail** |
| `domain_exclusion_asserted` | `out_of_domain` whose reason cites a code the oracle's own `d3_violations` licenses | pass |
| `domain_exclusion_unasserted` | `out_of_domain` with no/unknown/unlicensed reason | **fail** |
| `domain_exclusion_where_in_domain` | `out_of_domain` on a case the relation under test includes | **fail** |
| `accept_above_g_alpha` | `accept` on a case the oracle puts above G_α | **fail** |
| `missing_code_cache_exclusion` | oracle marks `e.code_cache`, checker does not report the cache exclusion | **fail** |
| `verdict_compared_agree` | accept/reject matches nearcore, case in domain | pass |
| `verdict_compared_disagree` | accept/reject differs from nearcore | **fail** |
| `verdict_agree_outside_domain` | accept/reject matches nearcore on an oracle-out-of-domain case | classified, not a verdict failure |

The licensing table (`EXCLUSION_LICENSES`) is explicit and tight. A code absent from it cannot license
an exclusion. The only documented relabel is `w.shape` licensing `e.mldsa_key`, taken from
`oracle/v3-d3/src/d3.rs:14` ("the checkers report `w.shape`"). A `e.wasm-α` reason licenses any of
`e.ood_host`, `e.float`, `e.eth_implicit_local`, `e.wasm-α`.

`--domain baseline|successor --widen CODE[,CODE...]` keeps expectation sets separate. Baseline (the
default, and what `checkD3` is) expects an exclusion exactly on the oracle's out-of-domain cases.
Successor moves the widened families into the domain and expects a nearcore-matching verdict there.
Every per-case record carries `expectation_domain`, so the two are never conflated. `--widen` without
`--domain successor` is rejected.

`--report FILE` writes `near-d3-difftest-report-v1`: the partition, per-checker totals, per-case
records (verdict, reason, oracle classification, classification bucket, licensing outcome), and an
explicit list of observables compared vs unavailable. It does not claim gas/refund/log comparison —
the checker emits only verdict and reason — and lists those as unavailable.

The original g_alpha and code_cache checks are preserved as hard failures, plus the reverse direction
(an oracle-marked code-cache case the checker does not exclude).

**`.github/workflows/ci.yml`** — split into three jobs:

* `difftest-gates` ("differential harness gates (schema)"): harness self-tests, the corpus-free
  `--verify-schema`, a step asserting the content gate fails closed (exit 2) with no corpora, and a
  step asserting a wrong schema string is rejected. Runs on every push, needs no corpora.
* `corpus-content-gates` ("corpus content drift gate (requires pinned corpora)"): the real digest
  check, gated on `vars.NEAR_CORPORA_AVAILABLE == 'true'`. When not configured GitHub reports it as
  **skipped**, which is visible and honest rather than a false green.
* `d3-drivers` ("d3 successor drivers (build + smoke)"): runs `make d3-drivers` (builds the named
  genesis, protocol-gas, D3α and float drivers) then `make d3-smoke` against a committed five-case
  fixture. New — nothing built or ran these in CI before.

**`Makefile`** — new `d3-drivers` and `d3-smoke` targets so CI and local runs share one definition.

**`oracle/wasm-d3/tests/d3_smoke/`** — `make_fixture.py`, `run_smoke.py`, and `cases/` (five real D3
cases copied verbatim from d3c7: in-domain accept, in-domain reject, code-cache exclusion,
`c.not_genesis` exclusion, `e.ood_host` exclusion; 180 KB total).

**`oracle/tools/test_difftest_d3.py`** — 22 tests: population shape, exhaustive partition, the 1,259
denominator, undefined-verdict and dropped-line handling, nine controlled-breakage controls,
baseline/successor separation, shard timeouts, and process-level exit codes plus report contents.
Discovered by the existing CI command `python3 -m unittest discover -s oracle/tools -p 'test_*.py'`.

**`oracle/wasm-d3/tests/l7_verify_all.sh`** — the D3 step now passes `--report`, writing the
machine-readable per-case partition per corpus.

---

## 2. Why the CI split rather than provisioning corpora

The workplan allows either provisioning or the split, and requires that a schema-only test "must not be
called a corpus-content drift check". I chose the split. Measured facts behind that decision:

```
$ du -sh /data/illia/nearproof-deps/corpora
8.5G    .
$ find /data/illia/nearproof-deps/corpora -type f | wc -l
707183
```

235,716 case directories, 5.79 GiB of hashed `claim.bin`/`witness.bin`/`meta.json` bytes. The corpora
are not committed, not published as an artifact, and can only be obtained by re-running the oracle
generator against pinned nearcore `TestEnv` chains — hours per seed on 16 cores. Uploading 8.5 GiB in
707k files per workflow run is not practical, and regenerating a small slice would produce a check that
looks green without covering the regression set. The split keeps the always-on check honest (schema
only, distinctly named) and leaves the content check honest and distinct on runners that mount the
corpora. If a self-hosted runner with the corpora is added later, set `NEAR_CORPORA_AVAILABLE=true` and
`NEAR_CORPORA_DIR`; nothing else changes.

---

## 3. Real command output

### 3.1 Manifest tool — all four modes, including the failure paths

```
$ python3 tools/d3/corpus_manifest.py --verify-schema docs/evidence/lean-chunk-L7/corpus-manifest.json
schema ok: docs/evidence/lean-chunk-L7/corpus-manifest.json (18 families, 6 corpora)
EXIT=0

$ env -u NEAR_CORPORA_DIR python3 tools/d3/corpus_manifest.py --verify docs/evidence/lean-chunk-L7/corpus-manifest.json
corpora root not configured: pass --corpora DIR or set NEAR_CORPORA_DIR (a manifest schema check needs neither: --verify-schema FILE)
EXIT=2

$ python3 tools/d3/corpus_manifest.py --verify docs/evidence/lean-chunk-L7/corpus-manifest.json --corpora /nonexistent/corpora
corpora directory not found: /nonexistent/corpora
EXIT=1

$ python3 tools/d3/corpus_manifest.py --verify docs/evidence/lean-chunk-L7/corpus-manifest.json --corpora /data/illia/nearproof-deps/corpora
verify: compared 18 families against docs/evidence/lean-chunk-L7/corpus-manifest.json
d1run          total= 53048  {'d1': 3394, 'mutants': 46009, 'ood': 3645}
d2corpus.v2    total= 67384  {'d2': 10537, 'mutants': 56457, 'ood': 390}
d3c7           total= 33248  {'d3': 5381, 'mutants': 27030, 'ood': 837}
d3c8           total= 49490  {'d3': 8192, 'mutants': 39997, 'ood': 1301}
d3c9           total= 15995  {'d3': 2656, 'mutants': 12928, 'ood': 411}
d3c10          total= 16551  {'d3': 2778, 'mutants': 13353, 'ood': 420}

all corpora match the counts the plan records
EXIT=0
```

Schema failure paths (each returns 1; the first line of stderr shown):

| mutation | exit | stderr first line |
|---|---|---|
| unmodified manifest | 0 | `schema ok: … (18 families, 6 corpora)` |
| missing `families` | 1 | `SCHEMA MISMATCH:` |
| wrong schema string | 1 | `SCHEMA MISMATCH:` |
| 3-char digest | 1 | `SCHEMA MISMATCH:` |
| negative count | 1 | `SCHEMA MISMATCH:` |
| family for unknown corpus | 1 | `SCHEMA MISMATCH:` |
| count for unknown corpus | 1 | `SCHEMA MISMATCH:` |
| non-hex digest | 1 | `SCHEMA MISMATCH:` |

Content failure paths:

```
$ # tampered digest in d3c9/ood
MANIFEST MISMATCH:
  - d3c9/ood.sha256: manifest '0000…0000' != measured '6fc1443db89809d785e7867aa39770461c60d29013f3c5b6a24b20221679ff57'
EXIT=1

$ # tampered case count in d3c9/ood
MANIFEST MISMATCH:
  - d3c9/ood.cases: manifest 1 != measured 411
EXIT=1
```

### 3.2 The CI job's steps, simulated verbatim with no corpora configured

```
$ python3 -m unittest discover -s oracle/tools -p 'test_*.py'
Ran 48 tests in 0.262s
OK (skipped=1)

$ python3 tools/d3/corpus_manifest.py --verify-schema docs/evidence/lean-chunk-L7/corpus-manifest.json
schema ok: docs/evidence/lean-chunk-L7/corpus-manifest.json (18 families, 6 corpora)

$ env -u NEAR_CORPORA_DIR python3 tools/d3/corpus_manifest.py --verify docs/evidence/lean-chunk-L7/corpus-manifest.json
corpora root not configured: pass --corpora DIR or set NEAR_CORPORA_DIR (…)
observed exit: 2
content gate refused to run without corpora (exit 2), as intended

$ # negative control: schema check rejects a malformed manifest
exit: 1 stderr: ['SCHEMA MISMATCH:', "  - schema is 'not-a-manifest', expected 'near-l7-corpus-manifest-v1'"]
schema check rejected a wrong schema string, as intended
```

`make workflow-lint` (zizmor 1.24.1 + actionlint 1.7.12 via Docker) exits 0 on the edited workflow:

```
 INFO zizmor: 🌈 zizmor v1.24.1
 INFO audit: zizmor: 🌈 completed .github/workflows/ci.yml
No findings to report. Good job! (1 suppressed)
EXIT=0
```

### 3.3 The comparison fix on all 115,284 saved verdicts

Run through the real CLI against the saved `lean.jsonl` per corpus (`--lean-from`), so this is the
production code path, not a re-implementation:

| corpus | cases | disagreements | partition |
|---|---|---|---|
| d3c7 | 33,248 | 0 | 729 asserted, 200 outside-domain, 32,319 verdict-agree |
| d3c8 | 49,490 | 0 | 1,126 asserted, 300 outside-domain, 48,064 verdict-agree |
| d3c9 | 15,995 | 0 | 342 asserted, 100 outside-domain, 15,553 verdict-agree |
| d3c10 | 16,551 | 0 | 351 asserted, 100 outside-domain, 16,100 verdict-agree |
| **total** | **115,284** | **0** | **2,548 + 700 + 112,036 = 115,284** |

Every one of the 2,548 exclusions now carries an asserted classification and a licensed reason code.
Re-counted from the four generated reports, the 1,259 population reproduces exactly:

```
total classification buckets: {'verdict_compared_agree': 112036,
                               'domain_exclusion_asserted': 2548,
                               'verdict_agree_outside_domain': 700}  sum 115284
ood-family exclusions: 2269
ood exclusions WITHOUT e.g_alpha (the 1,259 population): 1259
reason codes among the 1,259: e.wasm-α 710, w.shape 373, c.not_genesis 137, e.secp 36, c.segment 3
```

The 700 `verdict_agree_outside_domain` cases all carry `d3_violations = ["c.no_resharding"]` and all
sit in the `ood` family with verdict `accept`. That is the documented quotient the L7 log §4.4
describes (their only violation is a D2/claim-domain guard and nearcore itself accepts them). They
remain verdict agreements because nearcore agrees; they are now explicitly classified per case instead
of being an unnamed `ood_decided_by_lean` counter.

### 3.4 Old vs new on the same bytes — no population regressed

I ran the original `compare()` from `HEAD` and the new one over the same 115,284 saved verdicts:

```
d3c7: original_bad=0 new_bad=0
d3c8: original_bad=0 new_bad=0
d3c9: original_bad=0 new_bad=0
d3c10: original_bad=0 new_bad=0
TOTAL original disagreements=0  new disagreements=0
```

Zero disagreements is preserved; what changed is that 2,548 exclusions are now asserted instead of
2,548 of them being classified only incidentally.

### 3.5 Controlled breakage — wrong input must fail

Against the real d3c9 corpus via the CLI:

| control | exit | reported |
|---|---|---|
| one `accept` flipped to `reject` | **1** | `disagreements_with_nearcore=1` |
| one exclusion reason replaced with `out of domain (not.a.real.code)` | **1** | `disagreements_with_nearcore=1` |
| one verdict line dropped | **1** | `disagreements_with_nearcore=1` |
| committed `wrongchecker.py` (always `accept`), whole d3c9 corpus | **1** | 10,118 disagreements = 9,938 verdict + 149 above G_α + 31 missing code-cache exclusion; plus 262 outside-domain verdict agreements classified separately |
| successor expectations against the baseline checker (`--domain successor --widen e.float`) | **1** | 4 in-domain exclusions refused |
| hung checker shard (`--timeout 2`, a 30 s sleeper as `D3_CHECK`) | **1** | `FAIL: lean checker exceeded 2.0s on shard 0 (1 cases)`; report written with `"failure": "timeout"`, `"total_disagreements": null`, no partition |

The `wrongchecker.py` row is the strongest: an always-accept checker now fails 10,118 times, including
on the code-cache and G_α populations that the old short-circuit partly hid.

### 3.6 Drivers build and run; smoke fixture exercises all four

```
$ make d3-drivers
cd spec/lean/v3 && lake build nearspec-v3-check-d3g nearspec-v3-check-d3proto
Build completed successfully (163 jobs).
cd oracle/wasm-d3/lean && lake build nearspec-v3-check-d3 nearspec-v3-check-d3f
Build completed successfully (124 jobs).
d3 drivers built: spec/lean/v3/.lake/build/bin/nearspec-v3-check-d3g … nearspec-v3-check-d3f
EXIT=0
```

```
$ make d3-smoke
smoke: 5 cases, 4 drivers built and run, baseline partition {"domain_exclusion_asserted": 3, "verdict_compared_agree": 2}
  baseline  {'accept': 1, 'reject': 1, 'out_of_domain': 3}
  float     {'accept': 1, 'reject': 1, 'out_of_domain': 3}
  genesis   {'accept': 2, 'reject': 1, 'out_of_domain': 2}
  proto     {'accept': 1, 'reject': 1, 'out_of_domain': 3}
  successor widening: [{'case': 'd3c7-ood-00-h10002-s0', 'baseline': 'out_of_domain', 'genesis': 'accept', 'd3_violations': ['c.not_genesis', 'c.no_resharding']}]
  controlled breakage: 1 disagreement(s) from flipping d3c7-d3-00-h10004-s1
SMOKE PASSED
EXIT=0
```

Failure path — no binaries:

```
$ python3 oracle/wasm-d3/tests/d3_smoke/run_smoke.py --bin-dir /tmp/opencode/emptybin
FAIL: baseline driver missing: /tmp/opencode/emptybin/nearspec-v3-check-d3 (build it: …)
EXIT=1
```

### 3.7 The real genesis widening, measured on all 137 `c.not_genesis` cases

```
c.not_genesis cases: 137
d3g verdicts: {'accept': 137}
d3g produced 137 of 137

baseline (checkD3 expectations):
  partition: {"verdict_agree_outside_domain": 137}
  disagreements: 0

successor --widen c.not_genesis:
  partition: {"verdict_compared_agree": 137}
  disagreements: 0
```

The same d3g output is classified differently under the two expectation domains — which is exactly the
separation the workplan asks for. Under baseline expectations those 137 accepts agree with nearcore but
sit outside D3α; under successor expectations with `c.not_genesis` widened they are in-domain verdict
agreements.

### 3.8 Build-coverage measurement (why the third criterion needed real work)

A transitive import walk from `spec/lean/v3`'s three default targets (`NearSpecV3`,
`nearspec-v3-check`, `nearspec-v3-leaftest`):

```
library .lean files: 111  reachable from default targets: 61  NOT reachable: 50
```

The 50 include `GenesisD3.lean` and `ReshardingD3.lean` — the genesis and resharding modules — plus the
whole `NearSpecV3/Logged/` tree (22 files) and `Wasm/FloatAxioms.lean`, `Wasm/Segment.lean`,
`Wasm/DomainD3.lean`, `Wasm/ChunkStorage.lean`. Separately, `oracle/wasm-d3/lean` is not in
`LEAN_PROJECTS` at all, so `nearspec-v3-check-d3` — the checker the D3 difftests run — was never built
by CI either. `make d3-drivers` now builds all four by name and fails if a binary is absent.

---

## 4. W01 success criteria: passed vs open

| # | criterion | status | evidence |
|---|---|---|---|
| 1 | A clean hosted/job environment either obtains verified corpora and checks bytes or runs a distinctly named lightweight test; no dependency on an unprovisioned developer-local path | **met** | hardcoded path removed; `--verify-schema` runs corpus-free on every push; content job gated on `NEAR_CORPORA_AVAILABLE` and reported as skipped when absent; the fail-closed step asserts exit 2 with no corpora (§3.1–3.2) |
| 2 | The comparison report partitions every input exactly once, with no missing outputs; expected domain exclusions have an asserted reason/classification, not an unconditional pass | **met** | partition invariant enforced in `compare()`; 115,284 = 112,036 + 2,548 + 700 measured from four real runs; all 2,548 exclusions licensed; 1,259 population reproduced exactly (§1.2, §3.3) |
| 3 | Wrong verdicts, wrong observables, missing lines, crashes and timeouts make the appropriate gate fail | **met except "wrong observables"** | 22 unit tests + 6 CLI controls all fail correctly (§3.5): wrong verdict, unlicensed reason, dropped line, always-accept checker, wrong expectation domain, and a hung shard under `--timeout`. Crashes: a nonzero checker exit or absent binary fails (§3.6); a killed shard leaves missing verdict lines → `missing_output`. **Gas/refunds/logs/roots are not emitted by the checker, so "wrong observables" cannot yet be tested** — recorded as open below |
| 4 | Required successor modules and drivers are actually built by CI; CI definitions are exercised, not accepted solely because YAML contains a command | **met** | `make d3-drivers` builds genesis/proto/D3α/float drivers by name; `make d3-smoke` runs all four on five committed real cases and checks the contract including controlled breakage; both commands were run here, and actionlint/zizmor validate the workflow (§3.6–3.8) |
| 5 | Per-case outputs, package identities and manifests support W12–W14 without reconstructing provenance from scattered logs | **partially met** | `--report` writes per-case records with verdict, reason, oracle classification, licensing outcome and `expectation_domain`; the report names observables checked vs unavailable. **Package identities** (binary sha256 per driver, corpora manifest digest) are not yet embedded in the report — open |

### Open items with concrete next steps

1. **Observable contract (criterion 3, criterion 5).** The checker emits only `verdict` and `reason`.
   Comparing gas, refunds, logs, return data and roots needs the Lean driver to emit them. That is a
   Lean-source change in `spec/lean/v3` / `oracle/wasm-d3/lean`, which this lane is explicitly not
   allowed to edit. Next step: open a W01 follow-up owned by the integration owner to extend
   `MainD3.lean`'s JSON line (and the Python checker's) with `gas_burnt`, `gas_used`, `refunds`,
   `logs`, `return_data`, then extend `compare()` to assert them per case. The report already lists
   these as unavailable, so nothing overclaims in the meantime.
2. **Package identities in the report.** Add `binary_sha256` per driver and the corpora-manifest
   digest to the report's `checkers` block. Small, bounded change; not done here to keep the diff
   reviewable. Note this matters for W12–W14: without it a report cannot prove which binary produced
   it, so criterion 5 stays partially met until it lands.
3. **50 unreachable library files.** The import walk above shows 50 of 111 v3 library files are not
   reached by default targets. `make d3-drivers` builds the four *executables* but does not import the
   50 files. A one-line import of `GenesisD3`/`ReshardingD3` into `NearSpecV3.lean` would build them,
   but that is a shared-file edit (workplan §4 rule 2: integration-owner territory) and the successor
   API is W00's. Next step: hand the list to W00's owner; the recommended change is `import
   NearSpecV3.GenesisD3` and `import NearSpecV3.ReshardingD3` in `NearSpecV3.lean` after W00 publishes
   the successor module layout. I did **not** edit `NearSpecV3.lean`.
4. **The `--domain successor` path is exercised only on the five-case fixture and the 137
   `c.not_genesis` cases.** It has not been run against a successor driver over the full corpora
   (that would need a successor checker and successor expectations for every widened family, which is
   W12). Baseline is the fully measured path.
5. **Content gate is not exercised in CI today.** It is gated on a repo variable that is not set. The
   command works locally (§3.1); the honest statement is "distinct and correct, not yet running in
   CI".

---

## 5. Residual premises

* The 115,284 verdicts used for the accounting are the saved `lean.jsonl` files from
  `/tmp/opencode/l7-full`, produced by the prior L7 session. This session did **not** re-run the Lean
  checker over all four corpora; it re-ran the *comparison* over those saved verdicts and separately
  ran the real checker on a 40-case sample and on the five-case smoke fixture. So the per-case
  accounting is measured on saved output; the checker's determinism at full scale is inherited from the
  prior log's claim, not re-proved here.
* "0 disagreements" means 0 under the licensing contract above. It is not a claim of equivalence with
  nearcore and does not cover gas/refunds/logs/roots.
* The 700 `verdict_agree_outside_domain` cases are counted as verdict agreements because nearcore
  accepts them. A reader who requires the D3α classifier and the checker to agree on *domain* as well as
  verdict should read those 700 as a documented quotient, not as agreement. The report makes them
  visible per case.
* The five smoke cases are copied real cases; the fixture is not a regeneration and its expected
  verdicts come from the oracle's `meta.json`, not from a checker run.
* Corpora sizes in §2 are `du -sh` on this host's surviving copy.

---

## 6. Next executable step

Set `NEAR_CORPORA_AVAILABLE=true` and `NEAR_CORPORA_DIR` on a self-hosted runner that mounts
`/data/illia/nearproof-deps/corpora`, then run the new `corpus-content-gates` job once and confirm it
exits 0 against the committed manifest. That is the one W01 path implemented but not yet exercised in
CI. Independently, hand item 3's 50-file list to W00 and item 1's observable request to the integration
owner.
