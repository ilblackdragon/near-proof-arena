# Wasm evaluation time on the successor path (W02): proved arcs

After W02 raised the step budget to `wasmFuel`, evaluation time became the binding limit: the
worst zero-fee-control contract (`blocks4999`) needed about 1.7·10¹² interpreter steps for a
300 Tgas receipt (`../fuel-termination/README.md` §4). This change makes the compiled checker
execute zero-fee control runs in bulk, with a proof that the result is identical, and without
changing any definition.

Target: nearcore 2.13.4 (`44f7ae6c`), PV86. Checker before: `b65fe05c…` (main `e706998dc`).
Checker after: `51de6112…` (this change). Generator: `oracle/v3-successor` with the new
`eval-time` scenario (`d922d680…`).

## 1. What changed

`spec/lean/v3/NearSpecV3/Wasm/Arcs.lean`, now imported by `Wasm/ChunkStorage`,
`D3/FunctionCall` (and through it `Successor/StorageExecution` and the successor checker) and
`MainRuntime`:

* `runFast` is `step`'s dispatch with one extra branch. At a free `block`/`loop`/`end`/`nop`
  whose precomputed **arc** has its guard satisfied, it executes the whole run of such
  instructions as one jump, and fuses the `br` that ends the run when there is one. An arc
  consumes exactly the fuel of the steps it replaces.
* Proved, no `sorry`, axioms `propext`/`Classical.choice`/`Quot.sound`:
  `runFast_eq_run` (for every fuel, configuration and state, given a valid table),
  `arcsOf_valid` (the builder emits only valid arcs), and the call-level equalities
  `callEntry = callEntryArcs`, `runCall = runCallFast`,
  `runCallWithLimits = runCallWithLimitsFast` and `outcome = outcomeFast`.
* These four equalities are `@[csimp]` lemmas. The compiler substitutes the fast functions in
  every module compiled with them in scope. `run`, `runCall`, `RelD3`, `Tier.rel` and all proofs
  keep the original definitions. The kernel non-vacuity build
  (`HEAVY_MEM=40G heavy lake build NearSpecV3.Examples.RealCaseD3`) still succeeds: 634 s,
  20.7 GB peak.
* The arc table is built once per call (`runCallFast`), one backward pass per function. It
  holds an arc for every pc of a run, so a branch that lands mid-run still finds one. The build
  takes about 5 ms for a 10,000-instruction function.
* A fused charged `br` calls the real `charge`. When that charge does not continue, the arc
  returns `step` of the exact single-stepped state. The failure result is therefore the
  single-stepped one by definition (`fuseBr_eq`).

Probe that the compiled checker takes the fast path: the IR of `Successor/StorageExecution.c`
and `D3/FunctionCall.c` calls `runCallWithLimitsFast` and never `runCallWithLimits`. The
timings below confirm it.

## 2. Verdict identity (checker before vs after; 16 workers)

| population | tier | cases | identical verdict **and** reason | wall before → after |
|---|---|---|---|---|
| 577 fixtures (`combined/fixtures.txt`) | signed | 577 | **577** | 26.5 s → 26.7 s |
| 577 fixtures | allFeatures | 577 | **577** | 59.7 s → 60.2 s |
| 3,138 gap census | signed | 3,138 | **3,138** | 137.6 s → 133.7 s |
| 3,138 gap census | allFeatures | 3,138 | **3,138** | 355 / 361 s → 367 / 363 s (§2a) |
| full corpus (d1run, d2corpus.v2, d3c7–d3c10) | allFeatures | 235,716 | **235,716** | after: 3,813 s |

Each run was diffed per case against the earlier `b65fe05c` results (verdicts: corpus 76,207
accept / 159,414 reject / 95 out of domain, unchanged). Every population moved 0 verdicts and
0 reasons. Blind replay (`tools/mainnet-replay/blind_corpus.py`, allFeatures):

* fuel-termination: 14/14 match;
* eval-time (§3): 6/6 match;
* the 577 fixtures: 400 match, 175 nearcore-reject (not graded) and 2 `blind_error` ("prev_outcome_root
  still present in blinded claim.bin", a blinding-harness limit). Per case, the category and
  the emitted outputs are identical for the before and after checkers on all 577.

### 2a. Wall-time noise

Three other lanes shared the 32-core host, at load average 5–60. The first gap allFeatures
pair measured 326 s → 369 s while the load rose from 26 to 43 between the two runs. An
interleaved re-run (after, before, after, before; load 33–47) measured 367, 355, 363 and
361 s, that is +1.5 % ± noise, and its verdicts were again 3,138/3,138 identical.
On these populations the Wasm work is too small for the arcs to show. They neither win nor
lose measurably.

## 3. End-to-end pinned-nearcore fixtures (`eval-time` scenario)

`NEAR_SUCCESSOR_SCENARIO=eval-time gen --domain d3 --seed 2027 --chains 1 --blocks 30
--p-missing 0 --mutate-every 0 --code-mutant-p 0 --ood-cap 100000` gives a quiet 4-shard chain
with the `evalc` contract (`scenarios::eval_wat`, the shapes of `research/lean-arcs/gen_wasm.py`).
It has 120 honest chunks, all `cold_ok`. `tools/d3/collect_fuel_stress.py` gives
`manifest-e2027.json` (0 problems). nearcore reports every call as out of gas. `cases.tar.gz`
holds the 6 cases that apply the calls (`cases-index.json` lists their sha256s), and
`scenario-e2027.json.gz` is nearcore's outcome tree.

| call | nearcore | Lean before | Lean after |
|---|---|---|---|
| `blocks4999` 300 Tgas `(loop (block)×4999 br)` | out of gas | not run (≈ 10.6 h by linear scaling of 38.3 s at 0.3 Tgas) | **accept, 49.6 s** |
| `deep4999` 300 Tgas `(loop block×4999 br $l end×4999)` | out of gas | not run (hours) | **accept, 50.1 s** |
| `midrun4998` 300 Tgas (the `br_if` lands mid-run) | out of gas | not run (hours) | **accept, 61.9 s** |
| `blocks4999` 3 Tgas | out of gas | accept, 1,068 s | **accept, 0.75 s** |
| `pushpop4999` 3 Tgas (push 4,998 labels, charged group, pop them) | out of gas | accept, 510 s | accept, 151 s (3.4×) |
| `brif4999` 3 Tgas (`br_if` back-edge, not fused) | out of gas | accept, 463 s | accept, 207 s (2.2×) |

These are wall times at load average 45–50, so they are upper bounds. Peak RSS is 73–80 MiB. All 120 honest chunks of the run accept with the new checker (`replay_successor.py`, 120/120 `verdict_compared_agree`).

## 4. Fuel-termination fixtures (`../fuel-termination/`, 14 cases, allFeatures)

Sequential runs at load average 1.5–4:

| step | before | after |
|---|---|---|
| `blocks4999` 0.3 Tgas | 38.33 s | **0.07 s** |
| `blocks200` 5 Tgas | 28.35 s | **0.40 s** |
| `blocks200` 1 Tgas | 5.75 s | **0.12 s** |
| `nops` 300 Tgas | 7.07 s | 3.42 s |
| three `nops` 300 Tgas in one chunk | 21.82 s | 10.85 s |
| `spin` 300 Tgas (min of 5) | 11.38 s | 11.16 s |
| `count` 300 Tgas (min of 5) | 4.59 s | 4.89 s (+6 %) |
| `grow_loop` 300 Tgas (min of 5) | 2.90 s | 3.03 s (+4 %) |
| `memmax`, `memfill_loop`, `sha_loop`, `host_loop`, `recurse*` | 0.05–4.0 s | the same ±3 % |

All 14 accept before and after. The small slowdown on loops with no free control run (`count`,
`grow_loop`) is the residual cost of the extra branch. It does not appear in the probe (§5),
where `spin`/`mixed` are at parity.

## 5. Probe (`research/lean-arcs`: `arcprobe` vs `arcprobe-old`, `outcome pv86 …` at `wasmFuel`)

The two probe binaries have the same source text. Only `arcprobe` imports `Wasm/Arcs`, so its
`outcome` call is compiled to `outcomeFast` by `@[csimp]`. All output lines are identical.

| module | gas | single-step | arcs |
|---|---|---|---|
| `b4999` | 0.3 Tgas | 50,343 ms | 35 ms (1,438×) |
| `deep4999` | 0.3 Tgas | 59,924 ms | 62 ms |
| `midrun4998` | 0.3 Tgas | 42,952 ms | 66 ms |
| `pushpop4999` | 0.3 Tgas | 44,055 ms | 14,759 ms (3.0×) |
| `brif4999` | 0.3 Tgas | 39,771 ms | 17,079 ms (2.3×) |
| `b500` / `deep200` / `b5` | 3 Tgas | 95,176 / 24,403 / 1,406 ms | 567 / 493 / 646 ms |
| `b4999` / `deep4999` / `midrun4998` | **300 Tgas** | — | 40.4 / 31.7 / 33.0 s |
| `spin` / `nops` / `mixed` (min of 3) | 30 Tgas | 2,908 / 1,665 / 2,535 ms | 2,822 / 783 / 2,518 ms |
| `spin` / `nops` / `mixed` (min of 3) | 300 Tgas | 28,015 / 16,870 / 2,521 ms | 28,777 / 7,736 / 2,568 ms |

The 30/300 Tgas rows ran at load average about 35, and the 0.3 Tgas rows at about 26.

Minimum plain-arc length (`arcMinLen`), on `mixed` at 30 Tgas, min of 3: 2 → 2,562 ms, 4 → 2,558 ms,
8 → 2,741 ms, no plain arcs → 2,704 ms, single-step 2,543–2,623 ms. The prototype's L3 (short
arcs cost about 10 %) does not reproduce, because the cost is the table lookup and not the arcs.
The lookup is now done only at run instructions, and `arcMinLen = 2`.

## 6. What is still open

* **Push-then-pop across a charge** (`pushpop4999`) and **`br_if` back-edges** (`brif4999`)
  remain O(`max_blocks_per_function`) list cells per iteration. They are 2–3× faster, not
  O(1): about 3–4 h for 300 Tgas on this host, against about 12 h single-stepped. Labels are a
  `List Label` with per-label heights, so an arc that keeps `m` labels must materialize them.
  An O(1) bound for these shapes needs either a different label representation in `St` (a spec
  change) or arcs that span charged straight-line groups (a symbolic-label interpreter over
  every non-control `exec` arm). Fusing a taken `br_if` would fix `brif4999` alone.
  `pushpop4999` would remain.
* The logged mirror `Logged/WasmRun.runL` (D3L) has its own step loop and still single-steps.
  So does compiled code that calls `Wasm.run` directly (`oracle/wasm-d3/lean/FuelProbe`, which
  is meant to count steps).
* `else`/`if`/`br_table` are never part of an arc.

## Reproduce

```
cd spec/lean/v3 && lake build nearspec-v3-check-successor
cd research/lean-arcs && lake build arcprobe arcprobe-old && python3 gen_wasm.py MODS
arcprobe --run GAS MODS/b4999.wasm ; arcprobe-old --run GAS MODS/b4999.wasm
NEAR_SUCCESSOR_SCENARIO=eval-time $B gen --domain d3 --seed 2027 --chains 1 --blocks 30 \
  --p-missing 0 --mutate-every 0 --code-mutant-p 0 --ood-cap 100000 --out RUN
python3 tools/d3/collect_fuel_stress.py --source RUN --out manifest.json
python3 tools/d3/replay_successor.py --binary CHECKER --tier allFeatures --cases-file LIST --out OUT --jobs 16
python3 tools/mainnet-replay/blind_corpus.py --binary CHECKER --cases LIST --out OUT --tier allFeatures
```
