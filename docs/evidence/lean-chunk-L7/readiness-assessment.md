# L7 readiness assessment — plan §5 validation items

Date: 2026-10-23. Lane L7, worktree `/data/illia/nearproof-wt/lean-chunk-L7`, branch
`lane/lean-chunk-L7`, base `a5ef42e0c`. Target nearcore `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86.

Every number below was measured in this worktree on this date unless marked otherwise. Where an item
cannot be satisfied, the reason is stated and no count is claimed. This document is evidence *about*
the repository, not a certification: nothing here closes Gate A, B or C.

## Summary table

| §5 item | status | what exists | path |
|---|---|---|---|
| 1 target identity | **partial** | corpus-level commit + PV86 in each `summary.json`; oracle pin file; no manifest binding compiler/toolchain/param hashes/executable digests in one place | `oracle/NEARCORE_PIN`, `<corpus>/summary.json`, this lane's `corpus-manifest.json` |
| 2 directed tests | **partial** | per-family directed suites exist and execute (L2 float, L3 crypto, D1/D2/D3 corpora); breakage/ablation regressions demonstrated for floats (L2's switches) and by this lane's wrong-checker controls on D1/D3/manifest/UQ-014 — but **none for crypto hosts or the storage bound**. Note `CryptoTest.lean` is **absent from this branch and from `main`**; it lives only in L3's worktree (§2) | this branch: `oracle/wasm-d3/tests/*`, `oracle/wasm-d3/tests/wrongchecker.py`; L3's worktree: `oracle/wasm-d3/lean/CryptoTest.lean` |
| 3 generated ≥1000/family × 4 seeds | **partial** | L2 float: 149,462 cases reproduced on all 4 seeds (70,000 generated + 79,462 directed per seed), 0 diffs; D3 corpora: 8/12/4/4 chains; no generated suite for crypto/actions/hosts. **All float work lives in L2's worktree and `Float.lean` is absent here and on `main`** (§3.1) | `lean-chunk-L2` worktree: `oracle/wasm-d3/tests/difftest_float.py` (not on this branch) |
| 4 chunk integration | **partial** | whole-chunk verdict + **12** header-field checks inside Lean against the endorsed header — counted this session as 12 `check (H.…)` sites in the cited block: `prevStateRoot`, `prevOutcomeRoot`, `proposals`, `gasLimit`, `prevGasUsed`, `prevBalanceBurnt`, `prevOutgoingReceiptsRoot`, `congestion`, `bwRequests`, `proposedSplit`, `txRoot`, `encodedMerkleRoot` (the earlier "11" undercounted by one); emitted receipts/logs/return data NOT diffed against nearcore per case; **and on D3 the verdict itself is compared for only 112,736/115,284 cases** (§5.1) | `spec/lean/v3/NearSpecV3/ChunkValidationD2.lean:238-271` |
| 5 regression corpora | **satisfied with caveat** | D1 53,048 / D2 67,384 / D3 115,284 all replayed, **0 accept/reject mismatches on every case the comparison reaches**, content hashes recorded. **Evidential status:** D3's saved per-case outputs were independently re-joined and recounted this session (§5.3); D1 and D2 save only aggregate reports (no per-case JSONL), so for those the evidence is the driver's own comparison executing plus the negative controls that make it fail loudly. The "one command exited 0" for the whole sweep is a prior-log claim this session did **not** observe — the clean re-run was killed at D2 by another tenant's `pkill -9 -f nearspec` (§4.5b, lane log), so D1 and D2 were re-run standalone and **both completed with 0 disagreements** (D1 53,048 in 368.3 s/602.5 s; D2 67,384 in 1,502.7 s/51.2 s). *Caveat:* on D3 the comparison covers 112,736 of 115,284 cases; 1,259 verdicts are never compared and 700 accepted-out-of-domain cases are excluded by design (§5.1–5.2). *Not* proven byte-identical to the original generation (recipes not re-runnable here) | `docs/evidence/lean-chunk-L7/corpus-manifest.json`, `oracle/wasm-d3/tests/l7_verify_all.sh`, results in the lane log |
| 6 replay ≥1000 consecutive blocks | **absent** | a 1,378-height metadata census (not execution); 4 real mainnet fixtures for an *older* statement (`receipt-transfer-batch/v0`), not chunk-transition v3 | `docs/e2e-results/mainnet-replay-2026-10/samples.jsonl`, `oracle/fixtures/historical/cases/` |
| 7 formal checks | **partial** | `lake build` 162 jobs exit 0 (incremental, warm `.lake`); 10 theorems axiom-audited within the allowed set out of **624** declared in the tree; no `sorry`/`native_decide`/new axioms; **not** a clean-checkout rebuild, **no** runtime-path restriction audit; `spec/lean/v3` is in neither CI's job matrix nor `LEAN_PROJECTS` | `spec/lean/v3`, `.github/workflows/ci.yml:94`, `Makefile:32`, this document §7 |

---

## 1. Target identity — partial

What is recorded:

* `oracle/NEARCORE_PIN` — `repo`, `tag=2.13.4`, `commit=44f7ae6c…`, `protocol_version=86`.
* Every corpus `summary.json` carries `nearcore_commit: 44f7ae6cd7ef08bab604e20a473bf77e35d4c993`
  and `protocol_version: 86` — **verified in all six** this session (d1run, d2corpus.v2, d3c7, d3c8,
  d3c9, d3c10), not just a sample. Each also records its generator `seed` (d1run 5151, d2corpus.v2 6262,
  d3c7–d3c10 = 7, 8, 9, 10).
* Lean toolchain is pinned per project (`spec/lean/v3/lean-toolchain`); `lake --version` here is
  5.0.0-src+5045d00 / Lean 4.34.1.
* Executable digests measured this session:

| artifact | sha256 |
|---|---|
| `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3` | `528992988e0c72769fe909494b3e99a2dd3d4c78ad47ecf7acf7524603ecb42f` |
| `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-wasm` | `4ce100d191a4400da605b626192ecd9aadc820dcbb359fc91c62234d33cc3f12` |
| `spec/lean/v3/.lake/build/bin/nearspec-v3-check-d1` | `478a57f358ee937c881180026f2ce4830c5a3b829a7403d26fdf4ecb0e6fe439` |
| `spec/lean/v3/.lake/build/bin/nearspec-v3-check-d2` | `8df208c55a74a87349e671ea22a5b403c4367e05a76a0f9331dae8e434a49c34` |
| `/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness` | `2e8184320ccb05cc524b16415c10e20f473edb157a08b9c36e67a8ad03d4c129` |

(The harness digest is now recorded in full. The earlier draft showed `08b9c36e67a8ad03d4c129…`, which
is a slice from the *middle* of this same digest rather than its leading hex — misleading, because a
reader would take it for a prefix. The full value above is what `sha256sum` printed on 2026-10-23.)

All five digests were re-measured **after** this session's `lake build` and are byte-identical to the
values above, including `nearspec-v3-check-d1`, whose tree I rebuilt. So the rebuild did not perturb the
binaries, which is a small but real determinism check on the Lean build.

What is **missing** for the item as written ("record source commits, compiler/toolchain versions,
runtime parameters, oracle build recipe, executable hashes and commands in a manifest"):

* No single manifest binds all six. I searched every `*.json` in the tree for one that carries both the
  D1 and D2 counts: the only hits are this lane's `corpus-manifest.json` and four unrelated
  `docs/e2e-results/`/`research/` reports. None of them carries `toolchain`, `executable`, `compiler` or
  `nearcore_commit` keys (checked programmatically), and this lane's manifest carries only
  `corpora_root`, `digest_definition`, `expected_counts`, `families`, `measured_counts`, `schema`. So the
  six facts exist *scattered* across `oracle/NEARCORE_PIN`, per-corpus `summary.json`, `lean-toolchain`
  files and this document's tables — but nothing binds them together as the item asks. The runtime *parameters* are only partly pinned: there is no
  `86.yaml` in `core/parameters/res/runtime_configs/` (79/82/83/84/85 + `parameters.snap`), so the
  Lean `NearCfg` defaults cite the 85 snapshot. This is UQ-004's subject and is unresolved.
* The per-case `meta.json` records the nearcore *verdict* but not the nearcore commit; the commit is
  only in the corpus-level `summary.json`. A case copied out of its corpus loses its provenance.
* The oracle build recipe is `oracle/scripts/link-nearcore.sh` + a per-crate `cargo build`; nothing
  records the resulting binary's digest automatically. `make pin-check` verifies *source* pins
  (`spec/tools/check_oracle_pins.py`), not binary identity.
* `oracle/vendor/nearcore` is **not linked in this worktree** (`readlink -f` empty), so the oracle
  crates (`oracle/v3`, `oracle/v3-d3`, `oracle/d3-ttn`) cannot be rebuilt here. The corpora they
  produced are present and were replayed; the generators were not re-run. This is why item 5 below
  is "replayed, not regenerated".

## 2. Directed tests — partial

Executing directed suites that I ran and that compare against something real:

| suite | command | measured result |
|---|---|---|
| L2 float operator/gas/size | `float_nearcore.py --limit 12` (**L2's worktree**) | values 1,260 cases / gas 210 modules / size 140 modules, 0 disagreements |
| L3 ecrecover vectors | `nearspec-v3-test-crypto` (**L3's worktree**) | 161 total, 35 recovered, 126 rejected, 0 mismatches |
| L3 ecrecover edge | `nearspec-v3-test-crypto edge` | 20 total, 0 failures |
| L3 ecrecover host | `nearspec-v3-test-crypto host` | 23 total, 0 failures |
| L3 p256 vectors | `nearspec-v3-test-crypto p256` | 17 total, 0 failures |
| L3 p256 host | `nearspec-v3-test-crypto p256host` | 13 total, 0 failures |

All six were re-run on 2026-10-23 and printed exactly the strings in the "measured result" column.
Two of these suites (`float_nearcore.py`, the `nearspec-v3-test-crypto` binary) are **not in this
worktree**: they live in L2's and L3's worktrees respectively and are not on `main` or on this branch.
I ran them there rather than copying them, so their paths are stated explicitly and a reader can
reproduce or dispute them.

Independent check of L3's transcription: I re-read all 161 rows out of
`runtime/near-vm-runner/src/logic/tests/ecrecover-tests.json` in the pinned nearcore and compared
them field-by-field with the hardcoded table in `CryptoTest.lean` — **161/161 present, 0 mismatched**.
That matters because a transcription error would be invisible to the test that consumes the table.

**The item's harder half — "at least one regression experiment showing removal/breakage of the new
behaviour makes a targeted test fail" — exists for exactly one family.** L2's log records ablation
switches (`--instruction-level-metering`, `D3_TTN_ABLATE=--ablate-cache/--ablate-overlay`). I ran my
own ablations and they do fail as required:

| ablation | result |
|---|---|
| D3 difftest with a wrong verdict oracle (`D3_CHECK=…wrongchecker.py`) | exit 1, **38/60** disagreements |
| D1 difftest with a wrong checker on the Lean leg only | exit 1, **41,959** disagreements (= every case whose `expected_rel_d1` is false) |
| D1 difftest with the wrong checker on **both** legs (`--python …/wrongchecker.py` as well) | exit 1, **83,918** disagreements (= 2 legs × 41,959) |
| D3 `--python` third leg with 40 verdicts flipped in a saved `python.jsonl` | exit 1, `python: disagreements=40`, `lean-vs-python: disagreements=40` |
| UQ-014 reproducer at 1,000 globals instead of 66,000 | exit 1, "nearcore did not report LoadingError" |
| `uq014_wasmtime_branches.py` with a Lean stub printing `ok 0 0 - 0` | exit 1, both `LinkError` rows report "Lean did not abort" |
| `uq014_wasmtime_branches.py` with a harness stub printing `prepare-error Foo` | exit 1, both rows report "preparation rejected the module" |
| `corpus_manifest.py --verify` with one family digest zeroed | exit 1 (and exit 0 on the untampered manifest) |

The wrong-verdict oracle is now a committed artifact, `oracle/wasm-d3/tests/wrongchecker.py`, so these
controls are reproducible rather than ad-hoc. **Correction to an earlier draft of this document:**
it recorded the D1 control as `--lean …/wrongchecker.py --mode bool` and a count of 83,918. That
command cannot run — `difftest_v3_d1.py`'s argparse block has no `--mode` switch, so the process exits
with "unrecognized arguments". 83,918 is the *both-legs-wrong* count (2 × 41,959); the Lean-only leg
against a wrong checker is 41,959. Both were re-measured on 2026-10-23
(`/tmp/opencode/neg-d1.json` = 41,959; `/tmp/opencode/neg-d1-both.json` = 83,918), and both exit 1.

No lane provides a *mutation* regression for the crypto hosts or the storage bound. L3's 161/20/23
and 17/13 counts are directed vectors against nearcore's own JSON/Wycheproof data, not generated.

## 3. Generated tests ≥1,000 per family across 4 seeds — partial

Measured, and only for floats. **Path caveat:** `difftest_float.py` and `float_nearcore.py` are in
**L2's worktree** (`/data/illia/nearproof-wt/lean-chunk-L2/oracle/wasm-d3/tests/`), not on `main` and
not on this branch. Re-run there on 2026-10-23:

```
cd /data/illia/nearproof-wt/lean-chunk-L2/oracle/wasm-d3/tests
python3 difftest_float.py --cases 1000 --seed S   # S = 1,2,3,4
family=float cases=149462 opcodes=70 disagreements=0     (measured identical on all four seeds)
```

The comparison is Lean float ops against a **Python IEEE-754 reference** (`float_ref.py`), not against
nearcore; `float_nearcore.py` is the leg that puts nearcore on the other side (1,260 value cases + 210
gas modules + 140 size modules, 0 disagreements, re-measured 2026-10-23).

Reading the generator directly, `gen(cases, seed)` emits `cases` random pairs *per opcode* plus the
directed edge pairs. With `--cases 1000` that is 1,000 generated pairs × 70 opcodes = **70,000
generated comparisons per seed**, i.e. the ≥1,000 bar is exceeded ~70× per seed, and four distinct
seeds were run. Note the total 149,462 includes directed pairs; the generated-only count is 70,000.

For whole-chunk float coverage I counted the corpora rather than trusting the lane's figure: counting
`executed_contracts[*].float == true` over all 115,284 D3 cases gives **160** entries, all on the single
contract `d3float`. **But "160 vs L2's 26" is not a like-for-like comparison and an earlier draft of
this document wrongly framed it as an understatement.** L2's 26 is its *candidate* predicate — a case
whose metadata names `d3float`, whose `nearcore` verdict is `ok`, **and** which carries the `e.float`
violation — measured on one corpus (`d3c9`, `chunk_float.py`'s `DEFAULT_CORPUS`). I reproduced that
predicate exactly: `d3c9` = 26, and the same predicate gives 35 (`d3c7`), 80 (`d3c8`), 19 (`d3c10`) —
160 across the four corpora. That happens to equal the float-execution count because every
float-executing case is also `d3float` + `nearcore: ok` + `e.float`, so the two sets coincide here.
L2's "26 recorded chunks" is **correct for the predicate it states**, but it is a *one-corpus* count:
`chunk_float.py`'s default corpus is `d3c9`. Re-run with `--corpus` on each of the other three, the
same script reports 35/26/17 lifted for d3c7/d3c8/d3c10 respectively. So the honest summary is: one
float contract, 160 float-executing case directories across all four D3 corpora — L2's "26" is
accurate but scoped to d3c9, not a count over the whole regression set.

### 3.1 The structural reason the whole-chunk float cases are out-of-domain here

This branch's checker **cannot execute float semantics at all**, which is why the D3 sweep's float
coverage is only indirect. `spec/lean/v3/NearSpecV3/Wasm/Exec.lean:325` reads
`| .float _ => .unmodeled "float (out of domain)"` — every float instruction is classified unmodeled and
the case is rejected as `out_of_domain` before execution. `Validate.lean:270` rejects a float operator
earlier still (`throw "float operator (out of domain in D3α; validation not modelled)"`) and
`Validate.lean:293` rejects a float type, so the rejection happens at validation, before instantiation.
The float implementation lives in `NearSpecV3/Wasm/Float.lean`, which **is absent on this branch and
absent on `main`** (verified with `git cat-file -e main:spec/lean/v3/NearSpecV3/Wasm/Float.lean`; L2's
worktree has it as a 577-line addition among 28 changed files).

One defensive-looking fallback is worth naming so nobody mistakes it for a hole: `Exec.lean:366`'s
`evalConst` maps a float constant to `.i32 0`. That looks like a silent wrong answer, but validation
rejects float *types* (`Validate.lean:293`) before `instantiate` runs, so a validated module cannot carry
a float global initializer into `evalConst`. The fallback is unreachable on the accepted path; the real
statement is "float is refused, not mis-executed".

So there are two separate statements and they must not be merged:

* L2's *float operator* differential is real and compared: 149,462 cases against a Python IEEE reference
  across 4 seeds, 0 disagreements, plus 1,260 value cases against nearcore's own engine (all re-run this
  session and reproduced exactly).
* This branch's *whole-chunk* checker does not contain that implementation. On D3 corpora, its float
  handling is "declare out of domain", and 143 of the 160 float-executing case directories are then
  never compared to anything (§5.1). So "0 disagreements on 115,284 D3 cases" says nothing about float
  arithmetic being correct in the chunk path — it says the chunk path declines to run it, and the
  harness mostly does not check that decision.

That is a genuine integration gap between L2's work and this branch, not a measurement gap. The same
shape applies to L3's crypto hosts (`NearSpecV3/Wasm/CryptoHost.lean` absent here) and L5's storage
bound (`NearSpecV3/StorageBound.lean` absent here): those implementations exist only in their own
worktrees and are not merged into this branch or `main`. Everything this lane measured about them was
measured *in their worktrees* and is labelled as such.

Families with **no** generated comparison at ≥1,000×4 seeds:

* crypto hosts — directed vectors only;
* actions/receipts/hosts in D2 — the corpora have distinct chain seeds per corpus: D1 **12**, D2 **14**,
  D3c7 **8**, D3c8 **12**, D3c9 **4**, D3c10 **4** (measured from each `summary.json`'s `seed:` fields),
  so the "at least four recorded seeds" *count* is met several times over for every corpus. But these
  are seeds of a whole-corpus generator, not "generated comparisons per family" in the plan's sense, and
  they are not re-runnable here (`oracle/vendor/nearcore` unlinked) — so the seeds exist as recorded
  provenance, not as a reproducible generation recipe.
* storage accounting — L5 added zero tests (see §"lane-claim audit").

## 4. Chunk integration — partial

What the whole-chunk comparison really asserts. `checkD2Core` (`ChunkValidationD2.lean:114-271`)
compares the *endorsed header's* fields against Lean's recomputation:

* `prevStateRoot == root` (:242, :251), `prevOutcomeRoot == outcomeRootD1 out.outcomes` (:255),
  `prevGasUsed == out.gasUsed` (:258), `prevBalanceBurnt == out.balanceBurnt` (:259),
  `prevOutgoingReceiptsRoot == outgoingReceiptsRootD2 …` (:260), `congestion` (:261),
  `bwRequests` (:262), `txRoot` (:265), `encodedMerkleRoot`/`encodedLength` (:269-270),
  `proposals` (:256), `gasLimit` (:257), plus `proposedSplit.isNone` (:263).

So an `accept` is **not** a bare verdict: the chunk's claimed state root, outcome root, gas used,
burnt balance, receipts root, congestion info and bandwidth requests all had to match. That is
stronger than "verdict only", and I correct my own earlier reading on this point.

What is **not** compared per case against nearcore:

* emitted receipts' *bodies* and logs/return data beyond what the outcome/receipts roots commit to;
* refund amounts as separate columns;
* the receipt-level gas split.
  The D3 difftest compares the `accept`/`reject`/`out_of_domain` verdict; the roots/gas are compared
  *inside* Lean against the header, and the header's authenticity comes from nearcore having produced
  it. That is a genuine differential signal but it is **one-sided**: Lean must reproduce nearcore's
  header, but the harness does not additionally diff a per-case table of gas/refunds/logs against a
  nearcore-emitted table. The D3α op-level harness (`oracle/wasm-d3/tests/difftest.py`) *does*
  compare full outcome lines (status, burnt, used, return bytes, error) and the trie harness
  (`oracle/d3-ttn/difftest_ttn.py`) compares 11 per-key storage slots + wasm gas + ext gas — those
  are the two harnesses where observables are compared field-by-field. Neither runs on the D3
  corpora as a whole-chunk sweep.

Also absent: "tampered claims/witnesses" comparison per new family. The corpora contain
`mutants/` (byte-level tampering) and they are replayed, but the mutants are generated per corpus,
not per newly-added semantic family.

## 5. Regression corpora — satisfied, with an explicit caveat

All six corpora exist on this host and **were replayed**, not merely counted. The "0 disagreements"
column means "0 mismatches among the cases the comparison actually reaches" — see §5.1 for how many
that is per corpus:

A counting trap worth recording: `find d2corpus.v2 -type d` returns **67,398** directories, not 67,384,
because the corpus carries a `parts/` staging directory with 14 numbered subdirectories (`parts/0` …
`parts/13`) that have **no `meta.json`** and are not cases. Counting case directories as "subdirectory
with a `meta.json`" gives the plan's 67,384 exactly, and the total across all six corpora is the
recorded **235,716** (`53,048 + 67,384 + 33,248 + 49,490 + 15,995 + 16,551`). My first independent scan
counted 235,730 by including `parts/`, which is the kind of off-by-a-staging-dir error that makes a
number look corroborated when it is not. The per-corpus figures below use the `meta.json` predicate.

| corpus | cases | d3/d2/d1 | mutants | ood | verdict |
|---|---|---|---|---|---|
| D1 `d1run` | 53,048 | 3,394 | 46,009 | 3,645 | **0 disagreements** |
| D2 `d2corpus.v2` | 67,384 | 10,537 | 56,457 | 390 | **0 disagreements** |
| D3 `d3c7` | 33,248 | 5,381 | 27,030 | 837 | **0 disagreements** |
| D3 `d3c8` | 49,490 | 8,192 | 39,997 | 1,301 | **0 disagreements** |
| D3 `d3c9` | 15,995 | 2,656 | 12,928 | 411 | **0 disagreements** |
| D3 `d3c10` | 16,551 | 2,778 | 13,353 | 420 | **0 disagreements** |
| **D3 total** | **115,284** | 19,007 | 93,308 | 2,969 | **0 disagreements** |

**What was recounted, and how, differs by corpus — an earlier revision of this subsection overstated it
by saying "every one".** Measured state of the saved artifacts:

* **D3: per-case recount is possible and done.** `/tmp/opencode/l7-full/{d3c7,d3c8,d3c9,d3c10}/lean.jsonl`
  each carry one JSON line per case (4.9 MB for d3c7). I joined them against the on-disk directories and
  recomputed the comparison myself: d3c7 33,248/33,248 present, d3c8 49,490/49,490, d3c9 15,995/15,995,
  d3c10 16,551/16,551 — **0 mismatches**, with 0 missing.
* **D1 and D2: only aggregate reports exist, so no per-case recount is possible from these artifacts.**
  `/tmp/opencode/l7-full/d1.json` and `d2.json` are 9,974 and 30,578 bytes and contain summary/stats
  aggregates (`stats`, `summary`, `mutant_families`, `tx_coverage_*`), **not** one verdict per case —
  there is no `d1/lean.jsonl` or `d2/lean.jsonl` on disk (I checked; the D3 output dirs have one and the
  D1/D2 ones do not). For D1/D2 the honest evidence is the drivers' own `disagreements: 0` plus the
  independent D1 recount described next, not a per-case re-join.
* **D1 does have a separate, genuinely independent recount available.** `/tmp/opencode/neg-d1b.json`
  (the negative control's report) records 41,959 disagreements when the Lean leg is replaced by an
  always-accept stub — which equals the corpus's `expected_rel_d1: false` count. That is the non-vacuity
  proof, not a fidelity proof. The fidelity figure is the driver's own `disagreements: 0` on 53,048 cases,
  re-run standalone this session (§4.5b).

So "0 disagreements" for D1/D2 rests on the driver's comparison logic actually executing and returning 0
(which I verified by reading the code and by the negative control failing loudly), while for D3 it rests
additionally on an independent per-case re-join.

### 5.1 What "0 disagreements" actually compares — measured, not inferred

This is the most important qualification in the document, and both this lane's earlier drafts and the
lane log understated it. I re-implemented `difftest_d3.py`'s `compare()` control flow (lines 82–122)
against the 115,284 saved verdicts and the on-disk `meta.json` files, and counted how many cases reach
the `(verdict == "accept") == expected_rel` equality test at line 113.

Result: **112,736 of 115,284 D3 cases (97.79%) reach that test, and all 112,736 match. 2,548 cases
(2.21%) never reach it**, because the checker returned `out_of_domain` and the code takes the `continue`
at line 112 before the equality test. Within those 2,548:

* **1,289** are still *partially* checked — the classifier comparison at lines 96–108 (the `e.g_alpha`
  and `e.code_cache` conditions) does apply to them: 279 `mutants` cases whose only violation is
  `e.code_cache`, plus 1,010 `ood` cases whose violation set includes `e.g_alpha`. For these, Lean's
  out-of-domain decision and its boundary reason are compared against the oracle's violation set.
  (1,289 + 1,259 = 2,548, which is the recount's total `out_of_domain` count; an earlier revision of
  this subsection said "1,539" here, which was an arithmetic slip — 279 + 1,010 is 1,289.)
* **1,259 are entirely unchecked** — all in the `ood` family, with violation sets like
  `('c.not_genesis','c.no_resharding')`, `('e.ood_host',)`, `('w.shape',)`, `('e.eth_implicit_local',)`,
  `('e.float',)`. Lean said `out_of_domain` with a reason matching neither `g_alpha` nor `code_cache`,
  so neither classifier comparison fires and the `continue` at line 112 ends the iteration. These are
  cases where **nothing about Lean's decision is compared to anything**.

So the honest statement of item 5's D3 result is: "0 disagreements among the 112,736 cases that the
harness actually compares, with 1,259 cases (1.09% of the corpus) whose verdict was never compared to
nearcore at all, and 1,289 more compared only through the classifier condition." That is a real
differential signal, but "0 disagreements on 115,284 cases" is not what the comparison computes. The
previous text's "0 under the oracle's in-D3α classification" was directionally right but understated
the size and the absolute-unchecked subset.

The separately reported 700 `ood`-family cases Lean *accepts* are a different set from the 2,548: they
are `accept` verdicts (so they do reach the equality test at line 113) whose nearcore verdict is `ok`,
all with violation `('c.no_resharding',)` — 200/300/100/100 for d3c7/d3c8/d3c9/d3c10. They are counted
as `ood_decided_by_lean` and are **not** disagreements. See §5.2.

### 5.2 The 700 accepted-out-of-domain cases are excluded from the count, by design

Reading lines 113–121 exactly: the disagreement append for the `ood` family sits *inside* the
condition `if v == "missing" or (v == "accept") != bool(near)`. For the 700, `v == "accept"` and
`nearcore` is `ok`, so that condition is **false**; execution falls through to the `elif fam == "ood"`
branch at line 120, which only increments a stats counter. So the 700 never enter `bad`, and the
printed `disagreements_with_nearcore=0` is consistent with the stats line
`('ood_decided_by_lean', 'accept', 'True') 200` appearing beside it — the two coexist because the
`accept`/`ok` combination is deliberately not a disagreement.

Precision matters here, and an earlier revision of this subsection got it wrong in a way that overstated
the problem. I recounted all 700 and **every one has `expected_rel: true`** — i.e. nearcore itself
returned `ok` and *accepted* the call. So for these 700, Lean's `accept` and nearcore's `accept` **agree
with each other**; what disagrees is the oracle's *classifier*, which labels the case out-of-D3α. The
harness is therefore right not to count them as Lean-vs-nearcore disagreements. The honest reading of
the 700 is: "the oracle's domain classifier and nearcore's runtime verdict disagree on these 700 cases,
and Lean sides with nearcore." That is a finding about the classifier's calibration, not about Lean's
fidelity — and "0 disagreements with nearcore" is literally true for them.

§5.1's "1,259 entirely unchecked" is a disjoint set (those Lean calls `out_of_domain`, so the `continue`
at line 112 fires); the 700 are cases Lean calls `accept` and they do reach the equality test. The 700
are a subset of the 112,736 compared cases, not a fourth bucket — the table below states this.

A reader should therefore hold these numbers together, not one. The buckets below are **mutually
exclusive and sum to the total**, which the previous version of this table did not do (it listed the 700
as a separate row while they are a subset of the 112,736):

| bucket | count |
|---|---|
| Lean `accept`/`reject` compared to nearcore's verdict, and matches | **112,736** |
| &nbsp;&nbsp;— of which, Lean `accept`s while the oracle's classifier says out-of-D3α (nearcore also accepted) | *(700, already inside the row above)* |
| Lean `out_of_domain`, compared only through the g_alpha/code_cache classifier | 1,289 |
| Lean `out_of_domain`, not compared to anything | **1,259** |
| **total D3 cases** | **115,284** |

(112,736 + 1,289 + 1,259 = 115,284. The 700 accepted-out-of-domain cases are inside the 112,736, not
additional to it.)

This is a quotient the plan permits (item 4: "Respect the existing error-kind quotient"), but a reader
comparing "115,284 cases, 0 disagreements" against "2,548 cases whose verdict never reached the
accept/reject test" deserves both numbers in the same sentence.

**The float family lands almost entirely in the unchecked bucket.** Of the 160 D3 case directories where
a float contract actually executed (`executed_contracts[*].float == true`, all on `d3float`), **143 have
Lean's verdict reaching neither the accept/reject test nor the classifier test** — they are
`out_of_domain` on the float/ETH-implicit reason with no `e.g_alpha`/`e.code_cache` violation to check
against. Only 17 of the 160 are checked at all. So the D3 whole-chunk sweep, as written, does **not**
compare Lean's handling of the float family against nearcore's verdict for 143 of its 160 executions.
That matters for item 4 more than for item 5: the float semantics L2 built are exercised end-to-end in
160 whole-chunk cases, but 143 of those are verdict-unchecked here. (L2's own 149,462-case operator
difftest and its 1,260-case nearcore anchor are separate, and those *are* compared.)

### 5.3 Independent recount of the comparison and the three-way join

I did not rely on the harness's printed `disagreements=0`. I re-derived the comparison from the saved
`lean.jsonl` files in `/tmp/opencode/l7-full/{d3c7,d3c8,d3c9,d3c10}/` against the on-disk case
directories and their `meta.json`, applying the same quotient the harness applies (skip
`out_of_domain` verdicts, which §5.1 quantifies separately):

| corpus | cases | verdicts present | compared mismatches |
|---|---|---|---|
| d3c7 | 33,248 | 33,248 | **0** |
| d3c8 | 49,490 | 49,490 | **0** |
| d3c9 | 15,995 | 15,995 | **0** |
| d3c10 | 16,551 | 16,551 | **0** |
| **total** | **115,284** | **115,284** | **0** |

So "0 disagreements" survives an independent recount on the compared subset — the caveat is the size of
that subset (§5.1), not the correctness of the comparison on it.

The same way, I joined the saved per-case verdicts directly — `lean.jsonl` against `python.jsonl`, keyed
by case directory — and compared them pairwise for the Lean↔Python leg:

| corpus | Lean verdicts | Python verdicts | common keys | verdict mismatches |
|---|---|---|---|---|
| d3c7 | 33,248 | 33,248 | 33,248 | **0** |
| d3c8 | 49,490 | 49,490 | 49,490 | **0** |
| d3c9 | 15,995 | 15,995 | 15,995 | **0** |
| d3c10 | 16,551 | 16,551 | 16,551 | **0** |

That is an independent check of the Lean↔Python leg over all 115,284 cases with no reliance on the
harness's own counting. The Lean↔nearcore and Python↔nearcore legs I checked the same way by reading
each case's `meta.json.expected_rel` and re-deriving the comparison, which is how the §5.1 quotient
numbers were produced. Both the Lean and Python verdict distributions reproduce exactly what the lane
log recorded (d3c7 11,834/20,685/729 etc.), so the saved runs are the same runs the log describes.

Content hashes: `docs/evidence/lean-chunk-L7/corpus-manifest.json` (18 families; per-family case
count, byte total and an order-stable SHA-256 over `claim.bin`/`witness.bin`/`meta.json`). The drift
gate `tools/d3/corpus_manifest.py --verify <manifest>` re-walks and fails on any drift; I showed it
fails on a tampered manifest. Re-running the manifest generator in this session produced a byte-identical
`families` map and `measured_counts` to the committed file, and `--verify` on the committed manifest
exits **0**.

**One-command re-confirmation — status: partial this session.** `oracle/wasm-d3/tests/l7_verify_all.sh`
runs the whole §5 regression path in order and stops at the first failure: 28 harness self-tests, the
UQ-014 reproducers, the 18-family manifest drift gate, D1 53,048, D2 67,384, the four D3 corpora, and
`make pin-check`. An earlier full run on 2026-10-23 exited **0** with `ALL STEPS PASSED (full sweep)`,
output in `/tmp/opencode/l7-full`. **A clean re-run launched this session did not complete end-to-end**:
it passed steps 1–4 (D1 53,048 cases, 0 disagreements) and then its D2 child was `Killed` by a
concurrent lane's `pkill -9 -f "nearspec"` cleanup at 21:34:16 — not an OOM (40 GB free, no
`out of memory` in dmesg) and not a disagreement. So "the whole sweep exits 0" rests on the earlier run;
this session re-confirmed D1 standalone and re-ran D2 standalone, and measured each D3 corpus in its own
run. See the lane log §4.5b. Steps as measured:

| step | measured |
|---|---|
| 1 harness self-tests | 28 tests, OK |
| 2 UQ-014 `LoadingError` reproducer | divergence reproduced (exit 0 by design only while it still diverges) |
| 2b UQ-014 wasmtime branch table | both import-related `LinkError` rows reachable after preparation, both legs agree |
| 3 corpus manifest | 18 families, all six corpora match the plan's counts |
| 4 D1 | 53,048 cases, **0 disagreements**, Lean 193.3 s + Python 379.7 s (first run) / 368.3 s + 602.5 s (clean re-run under load 50) |
| 5 D2 | 67,384 cases, **0 disagreements** — earlier sweep Lean 645.5 s + Python 48.5 s; **standalone re-run this session Lean 1,502.7 s + Python 51.2 s, exit 0** |
| 6 D3 | 33,248 + 49,490 + 15,995 + 16,551 = 115,284, **0 disagreements** on each |
| 7 `make pin-check` | exit 0; **13 distinct challenge classes** `ok` across 16 ok lines |

Two independent full runs of D1 agree: the earlier run measured Lean 193.3 s + Python 379.7 s and this
session's clean re-run measured Lean 368.3 s + Python 602.5 s, both 53,048 cases / **0 disagreements**,
same `stats` (`d1.accepted_by_all` 3,394; `mutants.cases` 46,009; `ood.cases` 3,645). The wall times
differ by ~2× because the host load average was ~50 on 32 cores; the verdicts did not.

**One timing asymmetry I checked rather than assumed:** D2's Python leg reports 48.5 s for 67,384 cases,
while D1's reports 602.5 s for 53,048 — about 12× faster per case. That is large enough to suspect a
stubbed or short-circuited comparison, so I timed both checkers directly on 210 cases each:

| checker | 210 cases | verdict mix |
|---|---|---|
| `spec_check_v3_d2.py` | **2.89 s** | accept 84 / reject 56 / out_of_domain 70 |
| `spec_check_v3_d1.py` | **30.20 s** | — |

So the D2 Python checker genuinely is an order of magnitude faster per case (D1's checker does more trie
and receipt work), and it produces a varied verdict mix rather than a constant answer. The asymmetry is a
property of the two implementations, not evidence that the D2 leg skips work.

**One gap in this script, found while auditing it:** its D3 step (step 6) invokes
`difftest_d3.py CORPUS --shards N --save DIR` **without `--python`**, so as written it reproduces only
the Lean↔nearcore leg — not the three-way comparison §4.1b measured. The "one command reproduces the
regression result" claim therefore covers Lean-vs-nearcore on D3 and both legs on D1/D2 (whose scripts
take `--python` in their argument list), but not Lean↔Python on D3. I added an opt-in `--python-leg`
flag that appends `--python` to the D3 invocations; it is opt-in because it doubles the D3 cost. The
three-way result itself is measured and unchanged (`/tmp/opencode/l7-results/*-py/`, recounted in §5.3);
it just was not what the sweep's exit 0 asserted. A run with `--python-leg` was not completed inside
this session's budget, so the "one command" claim for the third leg remains *not* re-confirmed by a
single command — only by the per-corpus runs in §5.3.

Because each step's exit status is the difftest's own disagreement count, "the script exits 0" is a
real assertion and not a print-only check; I verified non-vacuity by feeding it deliberately wrong
checkers (see §"Gating findings").

**Caveat, stated plainly:** these are *replays of corpora that exist on this host*, and their counts
and content match the figures the plan records. They are **not** proven to be byte-identical to the
corpora as originally generated in the historical runs, because the generators could not be re-run
here (`oracle/vendor/nearcore` is unlinked, so `near-arena-oracle-v3-d1 gen --domain d1|d2|d3` cannot
be rebuilt). So this is an *exact replay of a surviving copy*, not a regenerated reproduction. The
manifest makes that checkable: if someone regenerates a corpus and its digest differs, the difference
is now visible.

The plan's "No previously accepted unchanged-domain case may silently regress" is satisfied for these
copies: every honest case that nearcore accepts is accepted by Lean and by the Python reference.

## 6. Representative replay ≥1,000 consecutive blocks — absent

What exists and what it actually is:

* `docs/e2e-results/mainnet-replay-2026-10/samples.jsonl`: **13,770 chunks over 1,378 distinct
  heights**, span 220,185,437–220,186,815 (1 missing height inside the span — 220,185,616), ten shard
  ids (1, 4, 6–13; 13,770 rows over 1,378 heights means shards are unevenly sampled),
  classified by workload (`d2-actions` 23, `d2-queues` 2, `d3-callbacks` 1306, `d3-calls` 2653,
  `d3-maxgas` 4256, `d3-nonwasm` 58, plus the rest). This is a **metadata census**, not execution —
  the plan explicitly says "Metadata-only workload classification does not satisfy this gate".
* `oracle/fixtures/historical/cases/`: **4** cases with authentic mainnet trie nodes and witnesses
  (shards 4/7/12/12 at heights 218,303,545–218,303,595). But their statement is
  `near/pv86/receipt-transfer-batch/v0` (`near/pv86/receipt-transition/v1`), **not** the
  chunk-transition relation, so they exercise `checkD1`-family semantics, not `checkD3`. Every case is
  class `historical-rebased-prestate`, and each `provenance.json` carries a `not_anchored` list. I read
  all four `anchors` maps directly this session; the failing anchors are:

| case | failing anchors |
|---|---|
| `mainnet-s12-h218303553` | `claim_pre_state_root_is_execution_chunk_prev_state_root` |
| `mainnet-s12-h218303595` | `claim_pre_state_root_is_execution_chunk_prev_state_root`, `receiver_records_identical_to_execution_prestate` |
| `mainnet-s4-h218303545` | `claim_pre_state_root_is_execution_chunk_prev_state_root`, `execution_chunk_contains_exactly_the_batch`, `claim_outcome_root_equals_onchain_prev_outcome_root` |
| `mainnet-s7-h218303557` | `claim_pre_state_root_is_execution_chunk_prev_state_root`, `execution_chunk_contains_exactly_the_batch`, `claim_outcome_root_equals_onchain_prev_outcome_root` |

  So the pre-state root is a *rebased earlier* root, not the root the chain applied to — these are not
  the chain's own transitions. (An earlier draft said "one case"; measured count is 4/4. An earlier
  draft also attributed the second failing anchor only to s4/s7; s12-h218303595 additionally fails
  `receiver_records_identical_to_execution_prestate`.) Even these 4 do not satisfy item 6 for the chunk
  transition.

No tool in the repo fetches mainnet chunk *state witnesses* and runs `checkD3` on them. The corpora
are synthetic chains from a deterministic generator. **Item 6 is absent.** The nearest honest
statement is: "4 authentic mainnet fixtures exist for an earlier statement; 13,770 chunks were
classified but not executed."

## 7. Formal checks — partial

Measured here:

* `cd spec/lean/v3 && lake build` → **Build completed successfully (162 jobs)**, exit 0.
* `#print axioms` over the chunk-transition surface (re-run 2026-10-23 with `lake env lean` against
  the built tree, so these are this session's outputs, not quoted):
  * `NearSpecV3.D3.relD3_iff_acceptsD3` → `[propext, Classical.choice, Quot.sound]`
  * `NearSpecV3.Wasm.Res.bind_assoc`, `seg_add`, `run_seg`, `foldSegments_eq_seg`,
    `run_foldSegments`, `pLE_ok` → same three.
  * `NearSpecV3.Wasm.noResharding_spec` → `[propext, Quot.sound]` — **note this one needs
    `import NearSpecV3.Wasm.DomainD3` explicitly**: the constant is NOT reachable from the root
    `NearSpecV3.lean`, so `#print axioms NearSpecV3.Wasm.noResharding_spec` against the root errors with
    `unknownIdentifier`. I had to write a separate file importing `DomainD3` to check it. That is the
    reachability gap restated as a measurement: the theorem exists and its axioms are fine, but the
    default build of `spec/lean/v3` does not reach it. Of 106 `.lean` modules in the tree, **51 are
    reachable from `NearSpecV3.lean` and 55 are not** (including all of `Wasm.DomainD3`, reached only
    through `oracle/wasm-d3/lean/Main.lean`).
  * `NearSpecV3.Wasm.TTN.ttn_costs_equal` → **no axioms**
  * `NearSpecV3.lift_ok` → `[propext]`
  * `NearSpecV3.rel_mono`, `inLang_mono`, `sound_lift` → same three (from the earlier pass).
  * L5's `StorageBound.Rec.guard_sufficient`, `Rec.size_le_recorded` → `[propext, Quot.sound]`;
    `removal_charge_can_exceed_limit`, `per_receipt_limit_does_not_bound_chunk` → no axioms.

  So ten theorems were checked in this session and every one stays inside the allowed set; this lane
  added **no** Lean theorems (its diff is Python + shell + Markdown only), so there is nothing new to
  `#print axioms`. **But "ten theorems" is not "all new theorems":** the v3 tree declares **624**
  theorems (`^theorem` across `NearSpecV3/`), so this audit covers ~1.6% of them. The plan's item 7 asks
  for "all new theorems' transitive axioms and runtime-path restrictions" — 10/624 does not meet that
  as written, and the honest status is "spot-checked the headline surface, not the closure".
* No `sorry`, `admit`, `native_decide` or new `axiom` declarations in the v3 tree — the only matches
  are two comments that *mention* those words
  (`Examples/Ed25519Kernel.lean:7`, `ChallengeChunkV3Gas.lean:34`).
* `decide +kernel` is used in **49** places. That is the kernel-checked `decide` (it re-elaborates and
  re-checks in the kernel), not `native_decide`, so those proofs are genuinely checked and their axioms
  are the standard set. Worth stating explicitly, because "49 uses of decide" would look alarming to a
  reader who conflated it with `native_decide`.

Not done: a from-clean-checkout rebuild (the worktree `.lake` caches are warm and were reused — the
162-job build was incremental, so "exit 0" does not prove a cold build works; `.lake` is 254 MB of
reused artifacts), an audit of "runtime-path restrictions" (i.e. whether each theorem's path hypothesis
is itself satisfied on real inputs), and `#print axioms` on *every* new theorem of *every* lane.

**The CI gap, verified in the workflow file rather than asserted:** `.github/workflows/ci.yml`'s `lean`
job matrix at line 94 is `project: [formal-core, spec/lean, zk-formal]` — `spec/lean/v3` is **not** in
it. `Makefile:32` sets `LEAN_PROJECTS ?= formal-core spec/lean`, also without v3. So neither CI nor
`make lean` builds the signed-surface v3 package; the 162-job build above was run by hand. A regression
in `spec/lean/v3` would reach `main` without any automated build noticing.

---

## Lane-claim audit (adversarial reading of the other lanes' logs)

| claim | verified? | finding |
|---|---|---|
| L2: floats complete, 1,260 + 210 + 140 against nearcore, 0 diffs | **yes** | reproduced exactly. Note the *operator* comparison is against a Python IEEE reference; only the nearcore anchor (1,260 values) is against nearcore's engine. |
| L2: 4 seeds × generated | **yes, but L2's *documented* run is below the bar** | L2's log documents `--cases 4`, which the generator turns into 4 pairs/opcode × 70 = **280 generated per seed, 1,120 over 4 seeds** — under §5's "≥1,000 per family" if read per-seed. Re-running `--cases 1000` gives **70,000 generated per seed** (149,462 total − 79,462 directed), so the bar is met by a *larger* run than the one L2 recorded. The generator supports it; L2's log just ran smaller. |
| L3: 161 ecrecover vectors, 0 mismatches | **yes, plus transcription audited** | table matches the pinned JSON 161/161 |
| L3: hosts are *not* reachable through `checkD3` | **yes** | `hostCall` in `Wasm/Host.lean` has no `ecrecover`/`p256_verify` arm; L3's `hostCall_no_arm` is honest |
| L3: "no whole-chunk case for ecrecover/p256" | **yes, and correctly reported as a gap** | the 83 ecrecover cases are all out-of-domain by construction |
| L5: `record_code_len` has no caller; bound is sound but not a protocol limit | **yes** | `record_code_len` (`core/store/src/trie/trie_recording.rs:148`) has zero call sites; `codes_to_record.insert` appears nowhere |
| L5: axiom claims | **yes, exactly** | reproduced all four |
| L5: "boundary cases below/at/above every limit" | **no evidence** | L5's diff added **no tests**; its 4 changed files are one `.lean` module, the root import, a spec doc and the log |
| D3 corpora "zero disagreements in the three-way comparison" | **yes, all three legs** | Lean↔nearcore 0, Python↔nearcore 0, Lean↔Python 0 on each of d3c7/d3c8/d3c9/d3c10 (115,284 cases). D1/D2 also ran the Python leg (0 diffs). |

## What this lane did NOT verify

Stated so nobody over-reads the table above:

* ~~The Python third leg on D3.~~ **Done after the first draft**: `difftest_d3.py --python` was run on
  all four D3 corpora against the saved Lean verdicts — Lean↔nearcore 0, Python↔nearcore 0, Lean↔Python
  0 on each (115,284 cases total). See the lane log §4.1b.
* The **generator provenance** of the corpora. They exist and their counts match the plan; the oracle
  crates that generated them cannot be rebuilt in this worktree (`oracle/vendor/nearcore` unlinked), so
  I replayed a surviving copy rather than regenerating from the pinned recipe.
* ~~The `--python` leg's own non-vacuity.~~ **Done after the first draft.** I took d3c9's saved
  `python.jsonl`, flipped 40 verdicts (`accept`↔`reject`) and replayed it through
  `difftest_d3.py --python --lean-from … --python-from …`: the report printed
  `python: disagreements_with_nearcore=40` and `lean-vs-python: disagreements=40`, exit **1**. So the
  comparison really compares — a changed Python verdict cannot pass silently. The `--python` leg's
  0/115,284 agreement is therefore a real assertion, not a print-only one.
* **Runtime-path restrictions** in item 7's sense: I read axioms for a handful of headline theorems, not
  for every new theorem with its path hypothesis. Concretely 10 of the 624 theorems declared in the v3
  tree, so ~1.6%.
* Anything about **succinct proof bytes, verification cost or proving resources** — outside this lane.

## Corrections this revision makes to the earlier draft

Listed so a reader can see what changed and why, rather than diffing prose. Each is a case where the
earlier text was wrong, understated, or asserted something I had not measured.

| earlier statement | corrected to | why |
|---|---|---|
| "0 disagreements" on D3 read as covering 115,284 cases | covers **112,736** compared cases; 1,289 classifier-only; **1,259 never compared**; plus 700 accepted-out-of-domain excluded (§5.1–5.2) | re-implementing `compare()` against saved verdicts |
| float coverage described as "160 whole-chunk executions" without noting comparison status | **143 of the 160 are never compared** (§5.1) | same recount |
| "one-command sweep re-confirms everything" | its D3 step omits `--python`, so it does **not** re-confirm the Lean↔Python leg; `--python-leg` flag added | reading the script's D3 invocation |
| "`evalConst` maps float to `.i32 0`" implied as a possible wrong answer | unreachable: validation rejects float types first (`Validate.lean:293`) | reading the validation path |
| "10 theorems checked" | 10 of **624** declared in the tree (~1.6%) | counting `^theorem` declarations |
| "CI does not build v3" | confirmed against `.github/workflows/ci.yml:94` matrix `[formal-core, spec/lean, zk-formal]` and `Makefile:32` | reading the workflow |
| "235,716 cases scanned" | still 235,716, but the naive `find -type d` count is 235,730 because `d2corpus.v2/parts/` holds 14 non-case staging dirs | measuring the predicate |
| "4 fixtures fail one anchor each" | per-case anchor lists differ; s12-h218303595 also fails `receiver_records_identical_to_execution_prestate` (§6) | reading each `anchors` map |
| wasmtime citations at "45.0.0" | the **pin** is 45.0.0 and the harness embeds it, but only 45.0.1/45.0.3 sources exist here; line numbers read from 45.0.3 | `ls` of the cargo registry |
| "D1 control = `--mode bool`, 83,918" | Lean-only is **41,959**; 83,918 is both-legs-wrong; `--mode` is not a D1 switch | running both controls |
| "1,539 `out_of_domain` cases are still partially checked" | **1,289** (279 mutants `e.code_cache` + 1,010 ood `e.g_alpha`); 1,289 + 1,259 = 2,548 | recounting by family and violation |
| "the 700 accepted-out-of-domain cases are excluded from the count" | they are **inside** the 112,736 compared cases and Lean **agrees with nearcore** on all 700 (every one has `expected_rel: true`); the *classifier* is what differs | recounting all 700 |
| "every one [of six runs] was independently recounted from its saved per-case `lean.jsonl`" | true for **D3 only**; D1/D2 saved aggregate reports with no per-case JSONL, so no re-join is possible for them | `ls` of `/tmp/opencode/l7-full/*/` |
| "the sweep exited 0 and re-confirmed §4" | the earlier run's exit 0 is a **prior-log claim not observed this session**; the clean re-run died at D2 from an external `pkill -9 -f nearspec` | observing the re-run |
| "sweep is reproducible by one command" (headline) | true as a script, but **not observed to exit 0 this session**; D3's third leg needs the new `--python-leg` opt-in | same |

The lane log (`docs/logs/lean-chunk-L7-2026-10-23.md`) carries the matching corrections in its §4.4b,
§4.5 and §4.6.

## Answers to UQ-014

**Branch-specific. `LoadingError` is reachable and unmodelled (a divergence); the import-related
`LinkError` branches are reachable and *are* modelled (both legs agree); `WasmUnknownError` has no
construction I could find; H2's concurrency-permit `LinkError` needs no concurrency — `try_acquire`
blocks on contention, so its only `None` path is counter overflow, making it effectively unreachable;
and the "memory export missing" `LinkError` is unreachable by construction.**

**Source citations re-verified against pinned nearcore this session** (checkout at
`/data/illia/nearproof-deps/nearcore`, `git log -1` = `44f7ae6 chore: prepare 2.13.4 mainnet release`,
matching `oracle/NEARCORE_PIN`). Each file:line the branch table relies on was read directly rather
than quoted from the earlier draft:

| citation | what it shows | confirmed |
|---|---|---|
| `runtime/near-vm-runner/src/prepare/prepare_v3.rs:310` | `if import.module != "env"` — the *only* module-name check on imports | yes |
| `prepare_v3.rs:315` | `// TODO: validate imported function types here.` — no name/signature validation | yes |
| `prepare_v3.rs:359-368` (`ensure_export_section`) | always appends a `memory` export in `VMKind::Wasmtime` | yes |
| `runtime/near-vm-runner/src/wasmtime_runner/mod.rs:745` | `.map_err(|err| VMRunnerError::LoadingError(err.to_string()))` on `Module::deserialize` | yes |
| `mod.rs:403-404` / `:410` | `C::Unknown { trap }` and the nondeterministic-trap arms producing `WasmUnknownError` | yes |
| `mod.rs:412-415` | `UnknownImportError` → `"unknown or invalid import"`, else `cause.to_string()`, wrapped in `LinkError` | yes |
| `mod.rs:747` | `LinkError { msg: "memory export missing" }` when the memory export is absent | yes |
| `mod.rs:1016` | `LinkError { msg: "failed to acquire execution slot" }` when `try_acquire` returns `None` | yes |
| `mod.rs:231-269` (`try_acquire`) | retries in a `while` loop, parks on `release_notify.wait(&mut guard)`; only `?` on `checked_sub`/`checked_add` at `:239,243,255,259` return `None` | yes |
| wasmtime `45.0.3/.../instance/allocator/pooling.rs:179` | `core_instance_size: 1 << 20, // 1 MiB` | yes |
| `pooling.rs:640-641` | `.context("module instance size does not fit in pooling allocator requirements")` in `validate_module` | yes |

**Version caveat on the wasmtime citations.** The pin is unambiguous — `oracle/NEARCORE_PIN`'s
`Cargo.toml:408` declares `wasmtime = "45.0.0"` and `Cargo.lock` resolves it to `45.0.0`, and the
built harness `/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness` embeds the
string `wasmtime-45.0.0`, so the *measurement* is against 45.0.0. But the only wasmtime sources
extracted on this host are **45.0.1** and **45.0.3**
(`/data/illia/cm-build/cargo-home/registry/src/index.crates.io-…/`); there is no `wasmtime-45.0.0`
tree to read. I verified `:179` (`core_instance_size: 1 << 20`) and `:640-641` (the `.context(…)`
message) in the **45.0.3** copy and they read as quoted; the line numbers agreeing across 45.0.x is
expected but is not proof that 45.0.0 is byte-identical. So the *behaviour* citations are measured
(the harness ran), while the *line numbers* are read from a neighbouring patch release. A reader who
needs the exact 45.0.0 lines must extract that crate; the `core_instance_size` default and the
context string are stable enough in 45.0.x that this is a low risk, but it is a gap and is stated as one.

Measured branch table (each row exercised against pinned nearcore's `prepare`+`run` and against
`nearspec-v3-wasm`; reproducer `oracle/wasm-d3/tests/uq014_wasmtime_branches.py`, exit 1 if any row
stops behaving as tabulated):

| branch | passes preparation? | nearcore | Lean | verdict |
|---|---|---|---|---|
| `LoadingError` (pooling `core_instance_size`, 1 MiB) | **yes** | abort `LoadingError`, 0 gas | **`ok`** | **DIVERGES** |
| `LinkError` "unknown or invalid import" (unknown `env` name) | **yes** | abort `LinkError` | abort `LinkError` | agree |
| `LinkError` "types incompatible" (known name, wrong signature) | **yes** | abort `LinkError`, wasmtime text | abort `LinkError`, fixed text | agree modulo `msg` |
| `LinkError` "memory export missing" | — | — | — | **unreachable**: `prepare_v3.rs:359-368` always injects the `memory` export |
| `WasmUnknownError` (`C::Unknown` / nondeterministic trap) | — | — | — | **no construction found** (see below) |
| H2 concurrency-permit `LinkError` ("failed to acquire execution slot") | — | — | — | **not measured**; needs concurrent chunk validations |

Why the `WasmUnknownError` and H2 rows are stated as they are rather than as "absent":

* `WasmUnknownError` fires at `wasmtime_runner/mod.rs:404` (`C::Unknown`) or `:410` (a
  nondeterministic trap). I read the exhaustive test this session at
  `runtime/near-vm-runner/src/wasmtime_runner/trap_classification.rs:100-118`
  (`test_all_wasmtime_traps_classified`): it iterates every `u8`, reconstructs each `Trap`, and asserts
  the classification is never `Unknown`, so a newly added unclassified trap variant would fail that
  test. That is a real argument, not a grep. The `:410` route needs `Trap::Interrupt`, i.e. epoch
  interruption; I re-grepped `runtime/` and `core/` for `epoch_interruption` and `consume_fuel` and both
  return **zero** hits in nearcore, so nearcore never enables either. So the *source* says unreachable,
  but I did not build a module that would exercise it, so I record "no reachable construction found"
  rather than "proven absent" — the proof covers "no known trap classifies as Unknown", not "no trap can
  ever reach the nondeterministic arm".
* H2's semaphore *does* have a failure return: `try_acquire` returns `Option` and
  `mod.rs:1012-1018` turns `None` into `VMOutcome::abort(…, LinkError { msg: "failed to acquire
  execution slot" })`. **But contention does not produce `None`.** Reading `try_acquire`
  (`mod.rs:231-269`) shows it retries in a `while` loop and parks on `release_notify.wait(&mut guard)`
  when the table/instance count is exhausted; the only `None` returns are the `?` on
  `checked_sub`/`checked_add` at `:239,243,255,259`, i.e. `u64` counter overflow/underflow. So the
  honest status is **effectively unreachable without a counter bug**, not "needs >1,000 concurrent
  instances". An earlier draft of this document said the latter; the source does not support it.
  This row therefore needs neither a Lean model nor an exclusion — but the inventory should say
  "unreachable absent arithmetic overflow", not "absent".

### `LoadingError`, in detail

Mechanism and citation:

* `runtime/near-vm-runner/src/wasmtime_runner/mod.rs:734-745` — `Module::deserialize` result is
  mapped to `VMRunnerError::LoadingError(err.to_string())`.
* `wasmtime-45.0.0/src/runtime/module.rs:540-552` — `Module::from_parts` runs the allocator's
  `validate_module`, whose instance-size branch is `pooling.rs:635-642` and whose message is the
  `.context("module instance size does not fit in pooling allocator requirements")` at
  `pooling.rs:640-641`; the size computation is `Instance::alloc_layout` (`pooling.rs:422-441`).
* The configured limit is `core_instance_size = 1 << 20` (1 MiB, `pooling.rs:179`); the instance
  layout grows with the module's defined globals (`VMGlobalDefinition` array).
* **The `LoadingError` path does not require a corrupted cache**, which is what H9's justification
  assumes. `with_compiled_and_loaded` (`mod.rs:687-745`) calls `Module::deserialize` on the module
  bytes whether they came from `cache.get` *or* from a fresh `compile_and_cache` (`:716-731`). So a
  freshly compiled module that exceeds the pooling instance size fails in `deserialize` on the
  ordinary cold path — no cache involvement at all. This is the part that makes H9's "a correct node
  never produces them" wrong: the correct node produces it.
* **Citations corrected after re-reading the pinned source this session** (an earlier revision named
  files that do not exist). The chain is: `Module::deserialize(...).map_err(|err|
  VMRunnerError::LoadingError(err.to_string()))` at `runtime/near-vm-runner/src/wasmtime_runner/mod.rs:744-745`;
  then `runtime/runtime/src/function_call.rs:328-330` matches `Err(VMRunnerError::LoadingError(msg))` and
  returns `Ok(VMOutcome::nop_outcome(FunctionCallError::LoadingError { msg }))`; and `nop_outcome` is
  defined at `runtime/near-vm-runner/src/logic/logic.rs:4511`, where it sets `burnt_gas: Gas::ZERO` and
  `used_gas: Gas::ZERO`. So it becomes a **0-gas** graceful `FunctionCallError::LoadingError` — a
  consensus-observable failed function call, not a chunk rejection. Note there are **two distinct
  `LoadingError`s** in this tree: the unrecoverable `VMRunnerError::LoadingError(String)` at
  `logic/errors.rs:23`, and the graceful `FunctionCallError::LoadingError { msg }` at `logic/errors.rs:56`;
  the conversion above is what bridges them. (Earlier text cited `logic/types.rs` for the nop path —
  that file contains no `nop_outcome` — and cited `function_call.rs:326-330` without the `runtime/runtime/src/`
  prefix, which is ambiguous because `runtime/runtime-params-estimator/src/function_call.rs` also exists.)
  nearcore's own test asserts this path (`runtime/near-vm-runner/src/tests/runtime_errors.rs:19-44`, using
  `near_test_contracts::contract_with_num_globals(100_000)`), and its comment says other VM backends
  "should run the contract successfully" — corroborating that this is a real, backend-specific,
  consensus-visible divergence rather than a spec artefact.

Measured boundary on this host, with `oracle/wasm-d3`'s harness against pinned nearcore:

| defined globals | nearcore | Lean `nearspec-v3-wasm` |
|---|---|---|
| 65,505 | `ok 490588602541 490588602541 - …` | `ok 490588602541 …` (agree) |
| 65,506 | `LoadingError("module instance size does not fit in pooling allocator requirements")` | — |
| 66,000 | same `LoadingError` | `ok 494363009716 …` (**diverges**) |

And the module **passes NEAR preparation**: instrumented size 454,039 bytes at 66,000 globals, far
under the 16 MiB `maxInstrumentedCodeSize`. So this is exactly "a contract that passes preparation"
whose execution nearcore refuses to load.

Reproducer: `oracle/wasm-d3/tests/uq014_instance_size.py` (asserts prepare-accept + LoadingError +
Lean-accepts; exit 0 only when the divergence reproduces, exit 1 when any leg changes). Negative
controls verified: 1,000 globals → "nearcore did not report LoadingError" → exit 1; a non-Lean binary
→ "the Lean spec did not return `ok`" → exit 1.

This is **not confined to a bare call**. `runtime/runtime/src/function_call.rs:93-143` converts the
aborted outcome into the receipt's action result: a `LoadingError` becomes an
`ActionErrorKind::FunctionCallError(...)` in `result.result`, and `gas_burnt` is incremented by
`outcome.burnt_gas` — which is zero. So inside a chunk, a FunctionCall receipt to such a contract
**fails with a LoadingError action result and burns 0 gas**, and the chunk is accepted. Lean, reaching
the same call, would succeed and charge the full operator gas. That changes the receipt's outcome, its
gas, and therefore the chunk's outcome root — a consensus-visible divergence, not merely an error-kind
difference. (Not demonstrated end-to-end through a chunk here, because building such a chunk requires
the oracle generator, which cannot be rebuilt in this worktree; the source chain above is the argument,
and it is a chain, not a measurement. Labelling it as testing would overstate it.)

Consequences for the plan's Gate B ("Every reachable supported-protocol row is implemented and
validated"; "Impossible cases have an explicit pinned-source justification"):

1. This is a reachable branch with a **consensus-visible outcome** (failed function call, 0 gas burnt)
   that `checkD3` cannot produce. Either `Prepare`/`Exec` must model the instance-size limit (which
   requires modelling Wasmtime's `Instance::alloc_layout`, i.e. a Wasmtime layout detail as a
   protocol condition), or L0 must mark this branch `impossible-at-boundary` **with a justification
   that survives this measurement** — and "H9/H10 assume absent" does not.
2. The precise globals threshold is a wasmtime-version detail (65,506 here), so a Lean predicate
   would be pinned to `wasmtime 45.0.0`'s layout. That is a legitimate "authenticated runtime
   environment assumption" the plan asks to enumerate, but it must be enumerated, not assumed away.
3. The resource `LinkError` branches are a *different* answer: they are reachable after preparation
   and both legs agree, so they are modelled and validated, not "absent". Measured above:
   unknown `env` import and incompatible import type both abort identically in nearcore and Lean.
   `WasmUnknownError` has no reachable construction I could build (see the reasons above), and H2's
   concurrency-permit `LinkError` needs no concurrency (it blocks on contention; only a counter
   overflow yields `None`). So UQ-014's answer is **branch-specific**: `LoadingError`
   reachable-and-divergent (measured); the two import-related `LinkError` branches reachable-and-agreed
   (measured); `WasmUnknownError` unresolved, with no reachable construction found; H2's permit branch
   effectively unreachable without an arithmetic-overflow bug.

4. **A correction to the inventory, not just to the hazard register.** L0's row `L0-W-007`
   (`spec/lean/v3/NearSpecV3/Wasm/Prepare.lean:478-490`) is marked `status: "validated"` with
   acceptance test "corpus LinkError cases". Two problems with that row: (a) the cited line range is
   `resolve`/`LinkResult`-adjacent but the link-error checks are actually at
   `Prepare.lean:464-474` (`linkError "unknown or invalid import"` at :471 and
   `linkError "*incompatible import type*"` at :474); (b) there are no `LinkError` cases in the corpora: scanning
   all 235,716 case `meta.json` files across d1run/d2corpus.v2/d3c7–d3c10 for the string `LinkError`
   or `unknown import` returns **zero**. The corpus `action_results` field records only the coarse
   label `"fail:FunctionCallError"` without the variant, so the corpora cannot distinguish a
   `LinkError` from any other function-call failure. The branch *is* validated — but by the two
   hand-built cases in `uq014_wasmtime_branches.py`, not by any corpus. `L0-W-007`'s "corpus LinkError
   cases" should be corrected to name that reproducer.

## Gate B mapping (§3), for the record

The plan's Gate B bullets, each against what this lane actually measured. None is closed by this work;
this only says which bullets now have measured evidence behind them and which are still assertion-only.

| Gate B bullet | this lane's evidence |
|---|---|
| inventory accounts for every branch/variant/instruction family/host/resource boundary/guard | not verified here; the 219-row inventory is L0's. This lane only audited one row (UQ-014). |
| every reachable row implemented and validated; zero unresolved exclusions | **UQ-014 contradicts the assumption** for `LoadingError`: a reachable, consensus-visible branch with no Lean model. |
| impossible cases have pinned-source justification + checked predicate | **UQ-014's "absent" framing is not justified.** `LoadingError` is measured reachable *and divergent*; the two import-related `LinkError` branches are measured reachable *and agreed* (so they need no exclusion, only a model that already exists); `WasmUnknownError` has no construction found, so "impossible" is unproven rather than justified; H2's permit branch is reachable in principle but unmeasured. |
| no prover-derived bound on the canonical relation | not this lane's; L1's `gAlpha` question is UQ-012. |
| protocol resource limits implemented, failure/rollback behaviour real | **partially**: L5's storage bound is proved sound but explicitly not a protocol limit (L5's own log), and the instance-size limit is unimplemented (UQ-014). |
| per-lane tests + combined regression/replay gates pass with zero unexplained disagreements | **regressions: 0 accept/reject mismatches on what the harness compares** (D1 53,048 + D2 67,384 + D3 115,284; D3's figure is 112,736 compared / 1,259 never compared / 700 excluded, §5.1–5.2). The prior log's `l7_verify_all.sh` exit 0 is **not** re-observed this session: the clean re-run died at D2 from another tenant's `pkill -9 -f nearspec`, so D1/D2 were re-run standalone and the four D3 corpora measured in separate runs. That script's D3 step also runs only the Lean↔nearcore leg (no `--python`, §5); **replay no** (§5 item 6 absent); per-lane tests partially audited. The plan's wording "zero unexplained disagreements" is met only for the compared subset. |
| all trusted assumptions enumerated, incl. runtime environment assumptions | **no**: the Wasmtime pooling-allocator limit and its 1 MiB constant are a runtime environment assumption that is neither modelled nor enumerated. |

## Gating findings

* `make lean` builds only `formal-core spec/lean` (`Makefile:32,158-165`); **`spec/lean/v3` is not
  built by the Makefile or by CI**. The signed-surface Lean package therefore has no automated build
  gate outside its own lane. Any regression in `spec/lean/v3` reaches `main` without CI noticing.
* `make pin-check` passes — `spec/tools/check_oracle_pins.py`, **exit 0**, 16 `ok` lines covering **13
  distinct classes** (the earlier "6 classes" figure in both documents was wrong). Precisely: 3 classes
  (`d0-missing`, `d0-quiet`, `d0-transfers`) checked against the **signed** `challenges/chl_640ed008….json`,
  and 13 classes against the **draft** `challenges/drafts/near-chunk-v3.draft.json`. It checks *source*
  digests only; it does not build or run the difftests.
* No difftest is wired into CI or the Makefile. Every differential result in this repository is a
  manual run. That is the structural reason "a harness that prints ok without comparing" is a live
  risk; I checked each of the eleven runnable differential scripts under `oracle/` and each exits
  nonzero on disagreement (`difftest_d3.py` via `sys.exit(1 if total_bad else 0)`, the rest via
  `sys.exit(0 if not disagreements else 1)` or `sys.exit(1 if bad else 0)`), and I
  demonstrated failure on wrong input for D1, D3 and UQ-014.

### Non-vacuity controls re-confirmed this session

The controls themselves are tabulated in §2; three of them were re-run on 2026-10-23 to confirm the
counts still hold rather than trusting the earlier draft:

| control | measured this session |
|---|---|
| `wrongchecker.py` as the D1 Lean checker | **exit 1, 41,959 disagreements** of 53,048 — matches §2's Lean-only figure exactly (report `/tmp/opencode/neg-d1b.json`) |
| `uq014_instance_size.py --globals 1000` | **exit 1**, "nearcore did not report LoadingError; got: ok 6565815766 …" |
| `uq014_wasmtime_branches.py --lean <stub printing 'ok 0 0 - 0'>` | **exit 1**, both `LinkError` rows report "Lean did not abort with LinkError" |
| committed `corpus-manifest.json --verify` | **exit 0** on the untampered file (tampered variant already shown to exit 1) |

Additional controls I ran independently this session (beyond the four above), so that "the harness
compares" is demonstrated rather than asserted:

| control | measured this session |
|---|---|
| `uq014_instance_size.py` honest run at the default 66,000 globals | **exit 0**, prints `[1] nearcore prepare: accepted (454039 instrumented bytes)`, `[2] nearcore run: LoadingError`, `[3] Lean …: ok 494363009716 …` — the divergence reproduces |
| `uq014_instance_size.py --lean <stub printing 'err 0 0 - 0'>` | **exit 1**, "the Lean spec did not return `ok`, so there is no divergence to report" — the script really inspects the Lean leg |
| `uq014_instance_size.py --globals 65505` vs `65506` | **65,505 → exit 1** ("nearcore did not report LoadingError; got: ok 490588602541 …"); **65,506 → exit 0** (LoadingError). The documented boundary is exact, and the script's behaviour flips across it |
| `uq014_wasmtime_branches.py` honest run | **exit 0**, both import-related `LinkError` rows reachable; unknown-import messages match textually, incompatible-type differs only in wording (message-modulo agreement) |
| `difftest_d3.py … --sample 40 --python` (the new `--python-leg` path) | **exit 0**, `lean: cases=40 disagreements=0`, `python: cases=40 disagreements=0`, `lean-vs-python: cases=40 disagreements=0` — the third leg executes rather than being a flag that does nothing |
| `difftest_d3.py … --sample 60` with `D3_CHECK=…wrongchecker.py` | **exit 1**, `disagreements_with_nearcore=38` of 60 |

So the "harness prints ok without comparing" risk is closed for the paths exercised here: each control
fails when the comparison should fail, and each honest run passes. The `--python-leg` control matters
specifically because that flag is *new in this lane* — an untested flag would have been a print-only
claim of my own making.
