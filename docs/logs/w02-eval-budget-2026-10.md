# Lane W02/W16 — evaluator speed and memory, size-limit fixtures (workplan items 2 and 4)

Worktree `.claude/worktrees/agent-a248c49a1bf71e546`, branch `worktree-agent-a248c49a1bf71e546`,
base `4f07a7fdf`. Shared host (32 cores, load 30–170 during the work; from 2026-10-30 ~00:20 the
coordinator capped replay/checker/generator processes at 4, honoured from then on).

## 2026-10-29

* Read the workplan. Baseline measurements with the base checker (`a1627ea3…`): 1 MB entropy-coded
  witness decodes in 90.5 s; gate-b 9.46 MB witness 38 s, 1,005 MB.
* gdb sampling (perf is unavailable: `perf_event_paranoid=4`; gdb must be the parent,
  `ptrace_scope=1`) of the zstd exe: every hot frame under `lean_byte_array_data`. Cause:
  `data.data.getD i 0` copies the input on every read. Fix: `getB` + `@[csimp] getB_eq`.
  1 MB: 90.5 s → 0.03 s. Batteries rerun, identical. Commit `ce80c592a`.
* gdb sampling of the checker on the 9.46 MB witness: time in `ArenaCore.SHA256_*` on `Nat`
  (bignum, `lean_cstr_to_nat`) called from NearSpecV3 (`merklizeBorsh`, `mkHStore`,
  `failedOutcomeD2`). `SHA256Fast`'s `@[csimp]` was never in scope there. Imported it in the four
  NearSpecV3 roots that see `NearSpec`/`ArenaCore` hashing. Gain on the witness fixtures is modest
  (40.8 → 38.4 s and 26.4 → 21.4 s CPU), memory unchanged.
* Label memo in `Wasm/Arcs.lean` (`runMemo`, `labsEqS` with `withPtrEq`, `brInfo`, `memoArc`,
  `memoBr`, `execM`, `fuseBrM`), proofs `runMemo_eq_runFast`, `memoOK_empty`, csimp chain re-proved.
  Two elaboration rounds (one `brIf` case of `execM_spec`, one `doBr_brInfo` case). Axioms clean.
* Generator: `eval-loops` and `code-response` scenarios in `oracle/v3-successor` (versioned
  generator; `make pin-check` ok). `ncref` (near-primitives without `test_features`).
  Discovered that the generator's nearcore build has `test_features`, which raises
  `MAX_COMPRESSED_STATE_WITNESS_SIZE` and both `MAX_UNCOMPRESSED_*` caps to 512 MiB — so the
  boundary verdicts come from `ncref`, the production build of the same crate.

## 2026-10-30

* `eval-loops` seed 2028: 144 honest chunks, all cold_ok; 10 loop cases. `code-response` seed 2029:
  120 honest chunks, all cold_ok; the three code chunks at 64 MiB / +1 B / half.
* Measurements and populations: see `docs/evidence/lean-chunk-completion/eval-budget/README.md`
  and `docs/evidence/lean-chunk-completion/size-limit-fixtures/README.md`.
* Corpus verdict identity was run on a deterministic 1-in-8 sample (29,465 of 235,716 cases) at
  2 workers, because of the process cap; the full corpus is left to the integrator's run.
* Verdict identity, before `a1627ea3…` → after `584976cf…` (verdict and reason per case): fixtures
  931/931 (signed and allFeatures), gap census 3,138/3,138 (both tiers), corpus 1-in-8 sample
  29,465/29,465 (allFeatures). Blind replay of the eval-loops cases + the 64 MiB code chunk: 11/11.
* 48 MiB family: 1,168 plain + 1,308 padded comparisons over 4 seeds, all agree, 0 Lean accepts of a
  nearcore reject. The padded run was cut from 1,200 to 446 cases to respect the process cap.
* Code-response family: at 64 MiB accept/accept, +1 B nearcore cache-dependent / Lean
  `w.code_response_size`, half accept/accept. One seed, no mutants.
* Default `lake build` passes (no `sorryAx`), `nearspec-v3-test-gate-b-caps` passes,
  `make pin-check` ok. `make d3-smoke` and the kernel non-vacuity build (`RealCaseD3`) were not run
  (host load; they touch no changed definition — the memo and the csimp imports change compiled
  code only).

Open: memory per witness byte (≈104 B) is unchanged; a natural (non-padded) 48 MiB witness and a
64 MiB decoded witness are not generated (§2 of the size-limit README gives the producer limits);
the corpus identity covers a 1-in-8 sample; the code-response family has one seed.
