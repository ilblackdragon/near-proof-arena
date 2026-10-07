# STATUS — lane/v3-d3 (handover, 2026-10-07)

Handover note for the next agent. **Nothing is signed, registered or deployed for `near-chunk-v3`.**

**Resumption, 2026-10-07 (recovery):** the `WasmRun.lean` proof repair now
builds the full `nearspec-v3-check-logged` executable and D0a tier (195 jobs). The repair
limits unfolding of `run`, uses `Nat.strongRecOn`, and retains the correct
names after dependent equalities substitute the host-call arguments. The eight
declarations in `oracle/wasm-d3/lean/AuditLogged.lean` have transitive axioms
exactly `{propext, Classical.choice, Quot.sound}`. The generated C for
`runUntil` uses a tail-loop jump.

The formerly failing `d3c7/ood/00-h10007-s1` completes and agrees with the
original checker on both verdict and reason (out of domain, `e.g_alpha`).
All 115,284 D3 cases pass three-way comparison and exact verdict/reason
comparison to the original checker. Original Lean and independent Python
baselines were reused with validated case sets and recorded hashes; fresh logged
outputs were measured. All 1,720 public D0/D1/D2/chunk fixture comparisons pass.
Full D2 results are recorded below; D1 and WASM/trie harnesses remain. Evidence and provenance:
`docs/e2e-results/v3-logged-checker/report.json`. New driver
`oracle/tools/check_logged.py` compares both verdict and reason, requires a
result for every input, and rejects crashes/truncated/duplicate output. Its
seven failure-handling unit tests pass. `make pin-check` passes. No live worker
has been stopped. The reference still uses the old necessity verifier.

Reproduce the proof/build audit from `oracle/wasm-d3/lean` using the required
`heavy` wrapper and CPU affinity:
`lake build nearspec-v3-check-logged NearSpecV3.ChallengeChunkV3`, then `lake env lean AuditLogged.lean`.
Run the comparison from the lane root as
`python3 oracle/tools/check_logged.py CORPUS --mode d3 --jobs 8 --save NEW_DIR`.
Use `--mode d2` for D2. `CORPUS` must use `claim.bin`/`witness.bin`; public arena
fixtures need temporary `claim.bin` links to their `request.bin` files.
The saved `logged.jsonl` is compatible with `difftest_d3.py --lean-from`.

**D2 full regression, 2026-10-07:** all 67,384 cases pass exact original/logged
verdict-and-reason comparison with both implementations freshly run. The fresh
logged results also agree with a fresh independent Python run and existing
nearcore corpus metadata on all cases (zero disagreements). Nearcore was not
rerun. Evidence: `docs/e2e-results/v3-d2-logged-checker/report.json` and
`three-way.json`; full JSONL is archived under the recorded validation paths.
`difftest_v3_d2.py` now rejects incomplete, duplicate, malformed and failed
checker output, supports digest-recorded saved results, and archives outputs.
Its eight tests and the seven logged-driver tests pass, as does pin-check.
The D1 corpus original/logged D2 comparison is in progress; this does not claim
that D1 and D2 have the same domain. The existing WASM/TTN harness driver still
uses the original WASM execution path and needs logged-path coverage.

Live state is in `docs/LIVE.md`. Main is at 0bb6fc8d+ (cost lane v1.8 deployed). This lane is main
plus everything below.

## 1. What this lane delivered (merged to main earlier)

* **D3α semantics.** WASM with Wasmtime/finite-wasm metering, all non-curve host functions, and a
  trie-backed `External` with trie-node accounting (`spec/lean/v3/NearSpecV3/Wasm/*`).
* **RuntimeD3.** `spec/lean/v3/NearSpecV3/D3/FunctionCall.lean` behind D2's `ActionHooks`, plus
  `checkD3`, the `G_α` cap and the domain conditions.
  - Spec: `spec/near-chunk-validation-d3.md`.
  - Evidence: three-way difftest, nearcore / Lean / independent Python
    (`oracle/tools/spec_check_v3_d3.py`), on 115,284 cases with 0 disagreements.
  - The D2 (67,384) and D1 (53,048) full regressions were identical to their committed reports.
* **Recursion track.** Closed as R5 (`docs/research/recursion-summary.md`). `G_α` is the key
  metric.
* **Contracts v1.7: coverage-tiered challenges.** `docs/CONTRACTS.md` §11, `docs/BENCHMARK_SPEC.md`
  §17.
  - Implemented in arena-types / worker / server / formal-checker: `coverage`, `declared_tier`,
    `prove` exit 3 = UNSUPPORTED, `COVERAGE_GAP_IN_TIER`, coverage report, tier-first board,
    `workload_suite.weight_source`.
  - The worker oracle dispatches per generator-spec tool (`ARENA_NEAR_ORACLE_V3` / `_D1` / `_D3`).

## 2. In progress: read-logging store refactor (lead decision A, option 1)

**Goal.** Every recorded-storage read of the D2/D3 relation goes through a logging store monad, so
that one `checkD3` run yields the exact read set. The D3a reference's normal form is then
`base_state` = exactly that set in byte order, and verify is one run plus a byte comparison.

**State.** These are commits on this lane, all under `spec/lean/v3/NearSpecV3/Logged/*` (new
files; the original definitions are untouched).
* `Store.lean`: the free store monad `SM`, with `run`, `reads`, `reads_restrict` (stores agreeing on
  `reads` give the same result) and the restrict fixed point.
* Lazy trie over the recorded store (`LazyTrie*`, `LazyFinalize`), with specs against `revealAll`.
* The D2 mirror:
  - Actions, Receipts, Queues, Runtime and Check.
  - **`checkD2L_eq : SM.run (storesOf wb) (checkD2L cb wb) = checkD2 cb wb`**, proved
    (`Logged/D2Check.lean:414`).
* The WASM machine with store reads in `SM` (`WasmStore`, `WasmCR*`, `WasmHR*`, `WasmStep*`,
  `WasmRun`), with storage host mirrors proved equal.
* The D3 FunctionCall mirror:
  - **`checkD3L_eq : SM.run (storesOf wb) (checkD3L cb wb) = checkD3 cb wb`**, proved
    (`Logged/D3LSpec.lean:206`).
* The API for the reference (`Logged/API.lean`): `checkD3Reads cb wb : Except String Unit × List
  (Nat × Bytes)`, `reads_restrict_eq`, `reads_fixed`, and the D2 variants.
* Driver `nearspec-v3-check-logged` (`--d2l`, `--d3`, `--d3l`; per-case ms).
  - On public-d2, all 339 cases are identical to `checkD2`, at the same speed.

**Proved at b27fea89.** `checkD2L_eq`, `checkD3L_eq`, `checkD3Reads_eq`, `checkD3_congr`,
`reads_restrict_eq` and `reads_fixed`, with axioms propext / Classical.choice / Quot.sound and no
sorry. No trusted file changed.

**Historical failure before recovery (now fixed; retained for context).**
* WIP commit b8633b30 replaces the deep `SM` recursion of the logged WASM run loop with a
  tail-recursive `runUntil` loop (`Logged/WasmRun.lean`).
* Why: the logged D3 checker at b27fea89 overflows the stack on long WASM runs (e.g.
  `d3c7/ood/00-h10007-s1`). That truncated its output on the d3c7 regression (33,248 cases,
  561 s), so there was no comparison.
* `runUntil_spec` has **2 unsolved goals**, around lines 335 and 357, both from unfolding `run`
  against the `callHost` match.
* Close them, rebuild, then do the steps below.
* Wrapper scripts are in `$SP/bin`: `d3l-check` for `D3_CHECK`, and `d2l-check` for `--lean`.

**Already run.** On public-chunk-v3 (407 positives), the original and logged checkers give
identical verdicts. Logged median 0.018–0.104 s per class (max 2.38 s); original median 0.022–0.123 s
(max 2.22 s).

**Not done:**

1. **Completed:** stack-safe loop, proof and guarded axiom audit.
2. **Full regressions with the logged checker.** Lead conditions require each to be identical to
   the committed report apart from timings:
   * D0 public: passed;
   * D1 `d1run` (53,048);
   * D2 `d2corpus.v2` three-way (67,384): passed, fresh original/logged/Python;
   * D3 three-way on `d3c7`/`d3c8`/`d3c9`/`d3c10` (115,284): passed.

   A first D3 run on `d3c7` crashed in `difftest_d3.py`, which hit a truncated JSON line: the
   checker's output was cut off when the job was stopped. Recovery rerun passed.
3. **Recheck the D1/D2 normal-form building blocks** (`examples/reexec-v3-d1|d2/formal`) against the
   spec.
4. **Performance.** One `checkD3Reads` run per case must fit the verify budget (old reference:
   median 0.04–0.37 s per class).
5. **Rebuild `examples/reexec-v3-d3` on the API.**
   * Normal form: ignored fields zeroed; entries normalised; `base_state ++ codes` = the read set
     in byte order.
   * Verify = one run + a byte-exact comparison.
   * Proofs `relD3_normal`, `normalW_sound`, `normalW_fixed` via `reads_restrict_eq` /
     `reads_fixed`; `checkD3_lockstep` from commit 1b8f2543 covers the field normalisations.
   * Remove the old necessity verifier (commit e08d133a: correct but too slow, `checkD3` once per
     value).
   * Then run check-local on `oracle/fixtures/v3/public-chunk-v3` and the held-out set; all gates
     must PASS. This includes ADVERSARIAL_PROOFS with the new `values/inject-unread` and
     `codes/inject-unread` mutators (c25d5f19).
   * Update `examples/reexec-v3-d3/README.md` and `docs/e2e-results/v3-d3-reference/`, which still
     describe the old escape clause.

## 3. `near-chunk-v3` challenge (single coverage-tiered challenge)

D0a now has a proved tier inclusion. Draft activation remains gated on final
domain bounds and workload-class coverage; the unsigned draft was not regenerated.

* **Draft.** `challenges/drafts/near-chunk-v3.draft.json` (+ `.measure.json`), built by
  `spec/tools/build_challenge_draft_v3_chunk.py`.
  - Unsigned id `chl_b44dc87154d4581cf125707b9dd0a7b3`. `arena-admin check` is OK with the
    lane-built `target/debug/arena-admin`; the live binary predates `weight_source`.
* **Statement.** `NearSpecV3.RelChunkV3 = RelD0 ∨ RelD1 ∨ RelD2 ∨ RelD3`
  (`spec/lean/v3/NearSpecV3/ChallengeChunkV3.lean`).
  - `rel_mono`, `inLang_mono`, `sound_lift`.
  - Formal tiers `d0a | d0 | d1 | d2 | d3a`, with `challengeParamsChunkWith` / `challengeParamsChunk t`, and
    `DomainTier` size-bounded at 64 MiB.
* **Settings.**
  - Scoring: `cost_v1`, `baseline_mode: paired`, the calibration block (pinned `arena-calibrate`),
    `verify_statistic: lower_quartile`. The scoring section is only emitted once a measured
    `cost_baseline` exists (`--baseline-summary`).
  - 13 workload classes (d0/d1/d2/d3 families), weights ASSUMED
    (`spec/challenge-inputs/near-chunk-v3-weights.json`).
  - Public fixtures `oracle/fixtures/v3/public-chunk-v3`: 407 positives, 244 rejections. D0–D2
    rejections are kept only where nearcore rejects, because out-of-lower-domain chunks can be true
    claims of the union.
  - Held-out set `/data/illia/nearproof-deps/heldout/near-chunk-v3` (commitment `sha256:eeeb27a4…`;
    secret seed file 0600 in that directory).
  - Caps: as D0, except verify is 60 s per batch.
* **Packages.** Reference `examples/reexec-v3-d3` (declared tier D3a) and hostile
  `adversarial/hostile-submissions/near-v3-d3-lenient-codes` (expected REJECTED). Both are pinned to
  the draft id; the re-pin checklist is in the builder docstring, and
  `cargo test -p proof-mutators --test packages` checks the pins.
* **Remaining before signing (lead's order).**
  1. Finish §2: proofs, regressions, the new reference, check-local.
  2. **RelD0a merge.** Lane `lane/v3-d0a-spec` (agent acfbe90cb4355de2a / spec lane
     a289835e29bfe1d92) adds additive-only `ChunkValidationV0a`/`ChallengeD0a`:
     - `RelD0a B`, `B0 = 2,000,000`, `InD0a B`, `relD0a_iff_inD0a`, `relD0a_relD0`.

     After it lands on main, merge it here and add the D0a tier: `Tier.d0a`,
     `RelTier .d0a = RelD0a B0`, a `rel_mono` case via `relD0a_relD0`, rank below D0 (renumber the
     ranks in the builder). The formal checker's splice table already maps `D0a → Tier.d0a`.
  3. **Re-freeze once.** The trusted tree must include the Logged modules and RelD0a:
     `arena-admin freeze-trusted` at the final commit, then rebuild the draft with
     `--freeze-commit <sha> --heldout-commitment sha256:eeeb27a4…`.
  4. **Joint w1 baseline window with the cost lane** (agent ac9bdd6c9c2cd20a5). Give them the final
     reference commit and the measure-draft path. Their procedure: `run_baseline.py --build-only`,
     then reference + 1 control session, with `--calibration-bin`, `--verify-statistic
     lower_quartile`, `--control-sessions 1`, and `--before-session` stopping w1. Feed the summary to
     the builder `--baseline-summary`.
  5. Sign with the operator tooling (never print key material), `arena-live register-challenge`,
     `arena-live build` + `install` (built into `~/.cache/nearproof-live-target`; workers need
     `ARENA_NEAR_ORACLE_V3_D1/_D3` and the chunk-v3 spec dir, public fixtures and held-out dir).
  6. Re-pin both packages to the signed id. Submit the reference (expect ADMITTED) and the hostile
     case (expect REJECTED), then record in `docs/LIVE.md` and `docs/e2e-results/`.
* **Succinct badge.** Designed (BENCHMARK_SPEC §17, thresholds in `CoverageSpec.succinct`), not
  implemented. It is post-launch.

## 4. Follow-ups (documented, not in this freeze)

* **B: union statement.** Restructure as `Rel_Dk := RelD3 ∧ InDk`; a successor statement is `RelD3`
  alone (CONTRACTS §11, "Known limitation").
* **Measured mainnet class weights** (replay), to replace the ASSUMED ones.
* **Clean-room VM.** It was black-box tuned against nearcore, not written from source.
* **`G_α`** is a checkpoint value (2²² · 822,756); re-fix it at checkpoint 5 from the measured rows
  per operator.
* **Held-out covert channel.** Publish only aggregate held-out coverage.

## 5. Corpora (scratchpad only; `SP=/tmp/claude-1002/-data-illia-nearproof/29f86fd5-cfb7-44c7-996e-70d81e3d17a4/scratchpad`)

| corpus | path | regenerate |
|---|---|---|
| D3 seed 7 / 8 / 9 / 10 (gas price 1e8) | `$SP/d3c7`, `d3c8`, `d3c9`, `d3c10` (+ `-dt2/` saved lean/python jsonl) | `oracle/v3-d3/scripts/gen-d3-corpus.sh` with OUT, SEED (7/8/9/10), CHAINS (8/12/4/4), BLOCKS=200, MUTATE_EVERY=20, CODE_MUTANT_P=0.25, OOD_CAP=25, DROP_CAP=48, CLEAN_PARTS=1; seed 10 adds `MIN_GAS_PRICE=100000000` |
| D2 full | `$SP/d2corpus.v2` (67,384) | see the corpus field of `spec/difftest-report-v3-d2.json` |
| D1 full | `$SP/d1run` (53,048) | `near-arena-oracle-v3-d1 gen --domain d1 --seed 5151 --chains 12 --blocks 150 --ood-cap 40 --mutate-every 4` |

The D3 oracle binary is built with
`CARGO_TARGET_DIR=oracle/d3-ttn/target RUSTC_WRAPPER= cargo build --offline` in `oracle/v3-d3`,
through `heavy` + `taskset -c 8-15,24-31`.

**Three-way D3 difftest:** `oracle/v3-d3/tools/difftest_d3.py CORPUS --python --shards 16 [--save DIR]
[--python-from FILE] [--lean-from FILE]`. Lean binary: `oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3`
(`lake build nearspec-v3-check-d3` in `oracle/wasm-d3/lean`). Python: `oracle/tools/spec_check_v3_d3.py`.

**D2 / D1 regressions:** `oracle/tools/difftest_v3_d2.py` / `difftest_v3_d1.py`, compared field by
field to `spec/difftest-report-v3-d{1,2}.json`.

## 6. Open nearcore findings and spec ambiguities

* **Contract-code verdicts depend on the cache.** nearcore's verdict on a witness missing a
  pre-state contract blob depends on the compiled-contract cache (a deploy precompiles, and a
  rollback does not evict) and on the preparation pipeline's order. `Rel_D3` is the cold-cache
  statement, and the cache-dependent cases are out of domain (`e.code_cache`;
  near-chunk-validation-d3.md §10.0).
* **Warm caches accept more.** A warm-cache nearcore validator accepts witnesses with no code blobs
  at all; `Rel_D3` rejects them.
* **Contract access list.** nearcore's contract access list is not minimal: deploys are tracked by
  hash regardless of account, and same-chunk deploy-and-call is never an access.
* **Prose-spec findings P1–P5** (`oracle/tools/README-d3.md`) are resolved in spec §10.0a:
  - P1: pre-state contract definition.
  - P2: G_α is evaluated after the main transition.
  - P3: excluded host functions are out of domain when called, not when imported.
  - P4: ML-DSA keys from contracts.
  - P5: ETH-implicit accounts, under the conservative rule.
* **Unread code blobs in the witness.** The witness may carry unread but valid preimages and unread
  code blobs that nearcore accepts. This is closed only once the §2 read-set normal form ships.
* **Open spec question.** It is unverified that `recorded_storage_size_upper_bound ≤ Σ values +
  2000·R` once contract-storage removals exist (spec §10, `w.size` argument).
